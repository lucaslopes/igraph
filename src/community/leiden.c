/*
   igraph library.
   Copyright (C) 2020-2025  The igraph development team <igraph@igraph.org>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

/*
 * =============================================================================
 * leiden.c -- Leiden community detection, disjoint and overlapping
 * =============================================================================
 *
 * WHAT THIS FILE IMPLEMENTS
 *
 *   1. The disjoint Leiden algorithm (Traag, Waltman & van Eck, 2019) for the
 *      Constant Potts Model and modularity-type objectives: local moving,
 *      refinement, aggregation, repeated on ever coarser graphs.
 *   2. A unit-l2 overlapping extension of the disjoint CPM hedonic game
 *      (Felipe, Avrachenkov & Menasche, Physica A 680:130989, 2025): every vertex holds
 *      a set of at most max_memberships labels, and local moving computes an
 *      exact best-response *set* by a sorted-prefix rule.
 *   3. Optional global limits on the number of occupied communities, and an
 *      opt-in diagnostic mode that records every accepted move and every
 *      multilevel proposal.
 *
 * HOW TO READ IT
 *
 *   The file is written bottom-up, as C requires: helpers come before the
 *   functions that use them, and the public entry points are at the end.
 *   A first reading works best top-down:
 *
 *     - Start at Section 5 (public API) to see what callers can ask for.
 *     - Follow the path you care about to its driver: Section 3.6 for
 *       partitions, Section 4.9 for covers.
 *     - From a driver, read the phase it calls (local moving, refinement,
 *       aggregation, token graph, guard), then the helpers of that phase.
 *
 *   Every section starts with a banner of the form
 *
 *       ============================================================
 *       Section N.M  Title
 *       ============================================================
 *
 *   followed by a short note on what the functions below it assume and
 *   guarantee. Searching for "Section 4.4.5", for example, jumps straight to
 *   the sorted-prefix best response.
 *
 *   Conventions used throughout:
 *
 *     - One function does one thing. A procedure with several steps is a
 *       short function that calls one helper per step, in order.
 *     - A workspace is a struct with a *_init / *_destroy pair. The caller
 *       zero-initializes it, registers *_destroy once on igraph's FINALLY
 *       stack, and then calls *_init; every *_destroy is safe on a partially
 *       initialized workspace. This keeps error unwinding in one place.
 *     - Floating-point expressions that decide moves are kept exactly as in
 *       earlier releases, statement by statement: splitting or reordering
 *       them changes floating-point contraction and therefore results.
 *     - Error messages are part of the observable contract and are unchanged.
 *
 *   Notation: n vertices, m edges; gamma is the resolution; w_e an edge
 *   weight; n_v a vertex weight. For covers, sigma_v is the sorted label set
 *   of vertex v, k_v = |sigma_v| and f_v = 1 / sqrt(k_v) its intensity; M is
 *   max_memberships. "Label" and "community" are used interchangeably;
 *   "cluster" is the disjoint word for the same thing.
 *
 * TABLE OF CONTENTS
 *
 *   Section 1  Shared numerics and utilities
 *     1.1  Tolerance and the improvement test
 *     1.2  Progress ceilings and interruption
 *     1.3  Default (unit) weight vectors
 *
 *   Section 2  Mass-ordered label index (used by both local movers)
 *     2.1  Order, storage and heap primitives
 *     2.2  Maintenance: rebuild, insert, remove, update
 *     2.3  Best-first queries
 *
 *   Section 3  Disjoint Leiden
 *     3.1  Options shared by every phase
 *     3.2  Local moving
 *          3.2.1  Workspace
 *          3.2.2  Removing and inserting a vertex
 *          3.2.3  Candidate clusters
 *          3.2.4  Choosing the best cluster
 *          3.2.5  The queue loop
 *     3.3  Refinement
 *          3.3.1  Workspace
 *          3.3.2  Well-connectedness
 *          3.3.3  Randomized merge of one vertex
 *          3.3.4  Renumbering refined clusters
 *     3.4  Aggregation
 *     3.5  Quality
 *     3.6  Multilevel driver
 *     3.7  Disjoint entry: start state, iterations and certificate
 *
 *   Section 4  Overlapping Leiden (unit-l2 CPM hedonic game)
 *     4.1  Model, notation and diagnostic records
 *     4.2  Cover utilities
 *     4.3  Potential (quality) of a cover
 *     4.4  Local moving
 *          4.4.1  Candidate buffer
 *          4.4.2  Workspace and label bookkeeping
 *          4.4.3  Candidate labels of one vertex
 *          4.4.4  Gains and the current score
 *          4.4.5  Sorted-prefix best response
 *          4.4.6  Applying a move
 *          4.4.7  Accepted-move trace
 *          4.4.8  The queue loop
 *     4.5  Token graph and projection
 *     4.6  One multilevel iteration
 *     4.7  Original-space guard and certificate sweeps
 *     4.8  Input validation and start covers
 *     4.9  Overlapping driver
 *
 *   Section 5  Public API
 *     5.1  igraph_community_leiden
 *     5.2  igraph_community_leiden_with_constraints
 *     5.3  igraph_community_leiden_with_diagnostics
 *     5.4  igraph_community_leiden_simple
 * =============================================================================
 */

#include "igraph_community.h"

#include "igraph_adjlist.h"
#include "igraph_bitset.h"
#include "igraph_constructors.h"
#include "igraph_dqueue.h"
#include "igraph_interface.h"
#include "igraph_memory.h"
#include "igraph_random.h"
#include "igraph_stack.h"
#include "igraph_structural.h"
#include "igraph_vector.h"
#include "igraph_vector_list.h"

#include "core/interruption.h"
#include "math/safe_intop.h"

#include <float.h>
#include <math.h>
#include <stdlib.h>


/* =============================================================================
 * Section 1  Shared numerics and utilities
 * =============================================================================
 *
 * Small helpers used by both the disjoint and the overlapping path.
 */

/* -----------------------------------------------------------------------------
 * Section 1.1  Tolerance and the improvement test
 * -----------------------------------------------------------------------------
 *
 * The overlapping mover (and the token-graph stage of the disjoint mover)
 * treat improvements smaller than a scale-aware margin as ties. This is a
 * private numerical convergence safeguard, not an algorithm parameter.
 */

/* The tie margin for comparing a and b: 64 machine epsilons, relative to
 * max(1, |a|, |b|). */
static igraph_real_t leiden_tolerance(igraph_real_t a, igraph_real_t b) {
    const igraph_real_t factor = 64.0 * DBL_EPSILON;
    const igraph_real_t scale = fmax(1.0, fmax(fabs(a), fabs(b)));

    return scale > DBL_MAX / factor ? DBL_MAX : factor * scale;
}

/* True if candidate exceeds current by more than the tie margin. NaN is
 * never an improvement; infinities compare directly. */
static igraph_bool_t leiden_is_improvement(igraph_real_t candidate,
                                           igraph_real_t current) {
    if (isnan(candidate) || isnan(current)) {
        return false;
    }
    if (!isfinite(candidate) || !isfinite(current)) {
        return candidate > current;
    }
    return candidate - current > leiden_tolerance(candidate, current);
}

/* True if a and b differ by at most the tie margin. */
static igraph_bool_t leiden_approximately_equal(igraph_real_t a, igraph_real_t b) {
    if (a == b) {
        return true;
    }
    if (!isfinite(a) || !isfinite(b)) {
        return false;
    }
    return fabs(a - b) <= leiden_tolerance(a, b);
}

/* -----------------------------------------------------------------------------
 * Section 1.2  Progress ceilings and interruption
 * -----------------------------------------------------------------------------
 */

/* A generous bound, 1024 * n * (max_memberships + 1), on queue pops and
 * accepted moves of one local-moving call. Reaching it signals unexpected
 * churn: the overlapping mover reports an internal error, the tolerant
 * token-stage mover ends its proposal. Saturates instead of overflowing. */
static igraph_int_t leiden_progress_ceiling(igraph_int_t n, igraph_int_t max_memberships) {
    igraph_int_t ceiling = 1024;
    igraph_int_t factor;

    factor = n > 0 ? n : 1;
    if (ceiling > IGRAPH_INTEGER_MAX / factor) {
        return IGRAPH_INTEGER_MAX;
    }
    ceiling *= factor;

    factor = max_memberships < IGRAPH_INTEGER_MAX ? max_memberships + 1 : IGRAPH_INTEGER_MAX;
    if (ceiling > IGRAPH_INTEGER_MAX / factor) {
        return IGRAPH_INTEGER_MAX;
    }
    return ceiling * factor;
}

/* Checks for a user interruption every `period` calls. The error is raised
 * with IGRAPH_ERROR from the frame that owns the caller's workspaces, so the
 * FINALLY stack unwinds them; the generic IGRAPH_ALLOW_INTERRUPTION macro
 * would return without doing so. */
static igraph_error_t leiden_check_interruption(int *counter, int period) {
    if (++*counter >= period) {
        *counter = 0;
        if (igraph_allow_interruption()) {
            IGRAPH_ERROR("Interrupted.", IGRAPH_INTERRUPTED);
        }
    }
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 1.3  Default (unit) weight vectors
 * -----------------------------------------------------------------------------
 *
 * A weight argument may be NULL, meaning "all ones". leiden_weights_t holds
 * either a borrowed caller vector or an owned vector of ones, so the phases
 * below always receive a real vector.
 */

typedef struct {
    igraph_vector_t ones;     /* owned storage when the caller passed NULL */
    igraph_vector_t *vector;  /* the vector to use: the caller's or `ones` */
} leiden_weights_t;

static void leiden_weights_destroy(leiden_weights_t *weights) {
    igraph_vector_destroy(&weights->ones);
}

/* Points `weights` at `given`, or at a new vector of `size` ones if `given`
 * is NULL. */
static igraph_error_t leiden_weights_init(leiden_weights_t *weights,
                                          const igraph_vector_t *given,
                                          igraph_int_t size) {
    if (given) {
        weights->vector = (igraph_vector_t *) given;
        return IGRAPH_SUCCESS;
    }
    IGRAPH_CHECK(igraph_vector_init(&weights->ones, size));
    igraph_vector_fill(&weights->ones, 1);
    weights->vector = &weights->ones;
    return IGRAPH_SUCCESS;
}


/* =============================================================================
 * Section 2  Mass-ordered label index (used by both local movers)
 * =============================================================================
 *
 * An index of the occupied labels of a local mover, ordered by mass and then
 * by identifier. It replaces linear scans for *omitted* labels: occupied
 * labels held neither by the moving vertex nor by any of its neighbours.
 *
 *   ascending order  (gamma * vertex weight > 0): the least massive omitted
 *     label is the only omitted label that can belong to a best response
 *     (Proposition "sparse candidate sets suffice"); ties prefer the smaller
 *     identifier, as the historical scans did;
 *   descending order (gamma * vertex weight < 0): omitted gains are positive
 *     and grow with mass, so only the most massive omitted labels can enter a
 *     best response (the disjoint mover takes one, the overlapping mover the
 *     first max_memberships plus rounding ties).
 *
 * Storage: a binary heap of label identifiers with a position map, keyed by
 * an external mass vector that the mover keeps current. A query walks the
 * heap best-first with a small auxiliary heap of positions (the frontier), so
 * it visits only the labels that precede the answer instead of every label.
 */

/* -----------------------------------------------------------------------------
 * Section 2.1  Order, storage and heap primitives
 * -----------------------------------------------------------------------------
 */

typedef struct {
    igraph_vector_int_t heap;      /* label identifiers in heap order */
    igraph_vector_int_t pos;       /* heap position of each label, -1 if absent */
    igraph_vector_int_t frontier;  /* best-first traversal queue of positions */
    const igraph_vector_t *mass;   /* external key, owned by the mover */
    igraph_bool_t descending;      /* true: most massive first */
} leiden_label_index_t;

/* True if label a comes before label b in index order. */
static igraph_bool_t leiden_label_before(const leiden_label_index_t *index,
                                         igraph_int_t a, igraph_int_t b) {
    const igraph_real_t ma = VECTOR(*index->mass)[a];
    const igraph_real_t mb = VECTOR(*index->mass)[b];

    if (ma != mb) {
        return index->descending ? ma > mb : ma < mb;
    }
    return a < b;
}

static void leiden_label_index_destroy(leiden_label_index_t *index) {
    igraph_vector_int_destroy(&index->frontier);
    igraph_vector_int_destroy(&index->pos);
    igraph_vector_int_destroy(&index->heap);
}

/* An empty index keyed by `mass`, addressable for labels below `cap`. */
static igraph_error_t leiden_label_index_init(leiden_label_index_t *index,
                                              const igraph_vector_t *mass,
                                              igraph_bool_t descending,
                                              igraph_int_t cap) {
    index->mass = mass;
    index->descending = descending;
    IGRAPH_VECTOR_INT_INIT_FINALLY(&index->heap, 0);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&index->pos, cap);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&index->frontier, 0);
    igraph_vector_int_fill(&index->pos, -1);
    IGRAPH_FINALLY_CLEAN(3);
    return IGRAPH_SUCCESS;
}

/* Keeps the position map addressable for every label below `cap`. */
static igraph_error_t leiden_label_index_reserve(leiden_label_index_t *index,
                                                 igraph_int_t cap) {
    const igraph_int_t old = igraph_vector_int_size(&index->pos);

    if (cap <= old) {
        return IGRAPH_SUCCESS;
    }
    IGRAPH_CHECK(igraph_vector_int_resize(&index->pos, cap));
    for (igraph_int_t c = old; c < cap; c++) {
        VECTOR(index->pos)[c] = -1;
    }
    return IGRAPH_SUCCESS;
}

/* Swaps heap positions i and j and updates the position map. */
static void leiden_label_index_swap(leiden_label_index_t *index,
                                    igraph_int_t i, igraph_int_t j) {
    const igraph_int_t ci = VECTOR(index->heap)[i];
    const igraph_int_t cj = VECTOR(index->heap)[j];

    VECTOR(index->heap)[i] = cj;
    VECTOR(index->heap)[j] = ci;
    VECTOR(index->pos)[cj] = i;
    VECTOR(index->pos)[ci] = j;
}

static void leiden_label_index_sift_up(leiden_label_index_t *index, igraph_int_t i) {
    while (i > 0) {
        const igraph_int_t parent = (i - 1) / 2;
        if (!leiden_label_before(index, VECTOR(index->heap)[i], VECTOR(index->heap)[parent])) {
            break;
        }
        leiden_label_index_swap(index, i, parent);
        i = parent;
    }
}

static void leiden_label_index_sift_down(leiden_label_index_t *index, igraph_int_t i) {
    const igraph_int_t size = igraph_vector_int_size(&index->heap);

    for (;;) {
        const igraph_int_t left = 2 * i + 1, right = left + 1;
        igraph_int_t best = i;
        if (left < size &&
            leiden_label_before(index, VECTOR(index->heap)[left], VECTOR(index->heap)[best])) {
            best = left;
        }
        if (right < size &&
            leiden_label_before(index, VECTOR(index->heap)[right], VECTOR(index->heap)[best])) {
            best = right;
        }
        if (best == i) {
            break;
        }
        leiden_label_index_swap(index, i, best);
        i = best;
    }
}

/* -----------------------------------------------------------------------------
 * Section 2.2  Maintenance: rebuild, insert, remove, update
 * -----------------------------------------------------------------------------
 */

/* Rebuilds the index from the labels with a positive member count, in
 * O(#labels). */
static igraph_error_t leiden_label_index_rebuild(leiden_label_index_t *index,
                                                 const igraph_vector_int_t *member_counts,
                                                 igraph_int_t nb_labels) {
    igraph_int_t size;

    IGRAPH_CHECK(leiden_label_index_reserve(index, igraph_vector_int_size(member_counts)));
    igraph_vector_int_fill(&index->pos, -1);
    igraph_vector_int_clear(&index->heap);
    for (igraph_int_t c = 0; c < nb_labels; c++) {
        if (VECTOR(*member_counts)[c] > 0) {
            VECTOR(index->pos)[c] = igraph_vector_int_size(&index->heap);
            IGRAPH_CHECK(igraph_vector_int_push_back(&index->heap, c));
        }
    }
    size = igraph_vector_int_size(&index->heap);
    for (igraph_int_t i = size / 2 - 1; i >= 0; i--) {
        leiden_label_index_sift_down(index, i);
    }
    return IGRAPH_SUCCESS;
}

/* Adds label c, which must not be in the index. */
static igraph_error_t leiden_label_index_insert(leiden_label_index_t *index, igraph_int_t c) {
    const igraph_int_t i = igraph_vector_int_size(&index->heap);

    IGRAPH_CHECK(leiden_label_index_reserve(index, c + 1));
    IGRAPH_CHECK(igraph_vector_int_push_back(&index->heap, c));
    VECTOR(index->pos)[c] = i;
    leiden_label_index_sift_up(index, i);
    return IGRAPH_SUCCESS;
}

/* Removes label c if present. */
static void leiden_label_index_remove(leiden_label_index_t *index, igraph_int_t c) {
    const igraph_int_t i = VECTOR(index->pos)[c];
    const igraph_int_t last = igraph_vector_int_size(&index->heap) - 1;

    if (i < 0) {
        return;
    }
    if (i != last) {
        leiden_label_index_swap(index, i, last);
    }
    igraph_vector_int_pop_back(&index->heap);
    VECTOR(index->pos)[c] = -1;
    if (i != last) {
        const igraph_int_t moved = VECTOR(index->heap)[i];
        leiden_label_index_sift_up(index, i);
        leiden_label_index_sift_down(index, VECTOR(index->pos)[moved]);
    }
}

/* Restores the heap order after the mass of an indexed label changed. */
static void leiden_label_index_update(leiden_label_index_t *index, igraph_int_t c) {
    const igraph_int_t i = VECTOR(index->pos)[c];

    if (i < 0) {
        return;
    }
    leiden_label_index_sift_up(index, i);
    leiden_label_index_sift_down(index, VECTOR(index->pos)[c]);
}

/* -----------------------------------------------------------------------------
 * Section 2.3  Best-first queries
 * -----------------------------------------------------------------------------
 *
 * Usage: leiden_label_index_begin(), then leiden_label_index_next() until it
 * returns -1. The frontier holds heap positions whose ancestors have been
 * yielded; popping the best of them yields labels in index order.
 */

static igraph_bool_t leiden_label_frontier_before(const leiden_label_index_t *index,
                                                  igraph_int_t p, igraph_int_t q) {
    return leiden_label_before(index, VECTOR(index->heap)[p], VECTOR(index->heap)[q]);
}

static igraph_error_t leiden_label_frontier_push(leiden_label_index_t *index, igraph_int_t p) {
    igraph_int_t i = igraph_vector_int_size(&index->frontier);

    IGRAPH_CHECK(igraph_vector_int_push_back(&index->frontier, p));
    while (i > 0) {
        const igraph_int_t parent = (i - 1) / 2;
        if (!leiden_label_frontier_before(index, VECTOR(index->frontier)[i],
                                          VECTOR(index->frontier)[parent])) {
            break;
        }
        const igraph_int_t tmp = VECTOR(index->frontier)[i];
        VECTOR(index->frontier)[i] = VECTOR(index->frontier)[parent];
        VECTOR(index->frontier)[parent] = tmp;
        i = parent;
    }
    return IGRAPH_SUCCESS;
}

static igraph_int_t leiden_label_frontier_pop(leiden_label_index_t *index) {
    const igraph_int_t top = VECTOR(index->frontier)[0];
    const igraph_int_t size = igraph_vector_int_size(&index->frontier) - 1;
    igraph_int_t i = 0;

    VECTOR(index->frontier)[0] = VECTOR(index->frontier)[size];
    igraph_vector_int_pop_back(&index->frontier);
    for (;;) {
        const igraph_int_t left = 2 * i + 1, right = left + 1;
        igraph_int_t best = i;
        if (left < size && leiden_label_frontier_before(index, VECTOR(index->frontier)[left],
                                                        VECTOR(index->frontier)[best])) {
            best = left;
        }
        if (right < size && leiden_label_frontier_before(index, VECTOR(index->frontier)[right],
                                                         VECTOR(index->frontier)[best])) {
            best = right;
        }
        if (best == i) {
            break;
        }
        const igraph_int_t tmp = VECTOR(index->frontier)[i];
        VECTOR(index->frontier)[i] = VECTOR(index->frontier)[best];
        VECTOR(index->frontier)[best] = tmp;
        i = best;
    }
    return top;
}

/* Starts a best-first traversal. */
static igraph_error_t leiden_label_index_begin(leiden_label_index_t *index) {
    igraph_vector_int_clear(&index->frontier);
    if (igraph_vector_int_size(&index->heap) > 0) {
        IGRAPH_CHECK(leiden_label_frontier_push(index, 0));
    }
    return IGRAPH_SUCCESS;
}

/* The next label in index order that is not yet a candidate, or -1 when the
 * traversal is exhausted. Exactly one marker is used: a nonzero entry of
 * int_marker, or a set bit of bit_marker, marks a label as a candidate. */
static igraph_error_t leiden_label_index_next(leiden_label_index_t *index,
                                              const igraph_vector_int_t *int_marker,
                                              const igraph_bitset_t *bit_marker,
                                              igraph_int_t *label) {
    const igraph_int_t size = igraph_vector_int_size(&index->heap);

    *label = -1;
    while (igraph_vector_int_size(&index->frontier) > 0) {
        const igraph_int_t p = leiden_label_frontier_pop(index);
        const igraph_int_t c = VECTOR(index->heap)[p];
        const igraph_int_t left = 2 * p + 1;
        if (left < size) {
            IGRAPH_CHECK(leiden_label_frontier_push(index, left));
        }
        if (left + 1 < size) {
            IGRAPH_CHECK(leiden_label_frontier_push(index, left + 1));
        }
        if (int_marker ? !VECTOR(*int_marker)[c] : !IGRAPH_BIT_TEST(*bit_marker, c)) {
            *label = c;
            return IGRAPH_SUCCESS;
        }
    }
    return IGRAPH_SUCCESS;
}


/* =============================================================================
 * Section 3  Disjoint Leiden
 * =============================================================================
 *
 * The algorithm of Traag, Waltman & van Eck (2019). One call of the
 * multilevel driver (Section 3.6) repeats three phases on ever coarser
 * graphs:
 *
 *   (1) local moving (3.2): visit vertices from a queue and move each to the
 *       cluster that most improves the quality;
 *   (2) refinement (3.3): inside every cluster, restart from singletons and
 *       merge well-connected subclusters, randomly with temperature beta;
 *   (3) aggregation (3.4): collapse every refined cluster into one vertex,
 *       starting the next level from the unrefined partition.
 *
 * The objective (Section 3.5) is, for undirected graphs,
 *
 *     Q = 1/(2m) sum_ij (A_ij - gamma n_i n_j) delta(s_i, s_j),
 *
 * with vertex out/in weights for directed graphs. Unit vertex weights give
 * the CPM; degrees with gamma / 2m give modularity.
 *
 * The same machinery runs on the token graphs of the overlapping path
 * (Section 4.5), in "tolerant" mode.
 */

/* -----------------------------------------------------------------------------
 * Section 3.1  Options shared by every phase
 * -----------------------------------------------------------------------------
 */

typedef struct {
    igraph_real_t resolution;             /* gamma */
    igraph_real_t beta;                   /* refinement temperature */
    igraph_bool_t allow_isolation;        /* may a vertex move to an empty cluster? */
    igraph_bool_t local_move_only;        /* skip refinement and aggregation */
    igraph_int_t max_total_communities;   /* upper bound on occupied clusters; -1 = none */
    igraph_int_t n_communities;           /* exact number of occupied clusters; -1 = none */
    /* Tolerant mode is used on the token graphs of the overlapping path,
     * whose weights 1/sqrt(k_u k_v) are rarely exact: gains within the tie
     * margin of Section 1.1 are ties, and a progress ceiling ends the local
     * moving instead of cycling on rounding noise. The original-space guard
     * of Section 4.7 then decides whether to keep the proposal. */
    igraph_bool_t tolerant;
} leiden_options_t;

/* -----------------------------------------------------------------------------
 * Section 3.2  Local moving
 * -----------------------------------------------------------------------------
 *
 * Vertices are examined from a queue, initially all vertices in random
 * order. A popped vertex is moved to the candidate cluster with the largest
 * gain; only strictly improving moves are made (ties beyond the margin in
 * tolerant mode). When a vertex moves, its neighbours outside the new
 * cluster are queued again. The membership vector is the starting point and
 * is updated in place.
 *
 * Candidate clusters of a vertex v (hedonic best response, Definitions 2/3
 * of Felipe et al., Physica A 680:130989, 2025):
 *
 *   - the clusters of its neighbours;
 *   - with isolation allowed, one recyclable empty cluster;
 *   - one extreme-mass *omitted* cluster whenever the empty cluster does not
 *     dominate all omitted clusters: with isolation disabled, with
 *     gamma * n_v < 0, with signed node weights, or when a count limit
 *     withholds the empty cluster.
 *
 * Count limits: an exact count never offers an empty cluster and keeps the
 * last vertex of a cluster in place; an upper bound offers an empty cluster
 * only while fewer clusters are occupied.
 */

/* ---- Section 3.2.1  Workspace --------------------------------------------- */

typedef struct {
    /* Inputs, borrowed from the caller. */
    const igraph_t *graph;
    const igraph_inclist_t *edges_per_vertex;
    const igraph_vector_t *edge_weights;
    const igraph_vector_t *vertex_out_weights;
    const igraph_vector_t *vertex_in_weights;    /* NULL for undirected graphs */
    const leiden_options_t *options;
    igraph_vector_int_t *membership;

    /* Derived flags. */
    igraph_bool_t directed;
    igraph_bool_t count_constrained;
    igraph_bool_t signed_node_weights;          /* an occupied mass may be negative */
    /* Undirected omitted-cluster queries use the label index of Section 2.
     * Directed masses depend on the moving vertex's in- and out-weights, so
     * directed graphs keep the linear scan, as do vertices whose weight has
     * the opposite sign of the resolution. */
    igraph_bool_t use_cluster_index;

    /* Clusters. */
    igraph_vector_t cluster_out_weights;         /* sum of member out-weights */
    igraph_vector_t cluster_in_weights;          /* directed graphs only */
    igraph_vector_int_t nb_vertices_per_cluster;
    igraph_stack_int_t empty_clusters;           /* recyclable empty cluster ids */
    igraph_int_t occupied_clusters;
    leiden_label_index_t cluster_index;

    /* The queue of unstable vertices. */
    igraph_dqueue_int_t unstable_vertices;
    igraph_bitset_t vertex_is_stable;
    igraph_int_t queue_pops;
    int interruption_counter;

    /* Candidates of the visited vertex; cleared after every visit. */
    igraph_vector_t edge_weights_per_cluster;
    igraph_bitset_t neighbor_cluster_added;
    igraph_vector_int_t neighbor_clusters;
    igraph_int_t nb_neigh_clusters;
} leiden_mover_t;

static void leiden_mover_destroy(leiden_mover_t *mover) {
    igraph_vector_int_destroy(&mover->neighbor_clusters);
    igraph_bitset_destroy(&mover->neighbor_cluster_added);
    igraph_vector_destroy(&mover->edge_weights_per_cluster);
    igraph_bitset_destroy(&mover->vertex_is_stable);
    igraph_dqueue_int_destroy(&mover->unstable_vertices);
    leiden_label_index_destroy(&mover->cluster_index);
    igraph_stack_int_destroy(&mover->empty_clusters);
    igraph_vector_int_destroy(&mover->nb_vertices_per_cluster);
    igraph_vector_destroy(&mover->cluster_in_weights);
    igraph_vector_destroy(&mover->cluster_out_weights);
}

/* Queues every vertex once, in random order (the only use of the random
 * number generator by local moving). */
static igraph_error_t leiden_mover_init_queue(leiden_mover_t *mover, igraph_int_t n) {
    igraph_vector_int_t vertex_order;

    IGRAPH_CHECK(igraph_bitset_init(&mover->vertex_is_stable, n));
    IGRAPH_CHECK(igraph_dqueue_int_init(&mover->unstable_vertices, n));
    IGRAPH_CHECK(igraph_vector_int_init_range(&vertex_order, 0, n));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &vertex_order);
    igraph_vector_int_shuffle(&vertex_order);
    for (igraph_int_t i = 0; i < n; i++) {
        IGRAPH_CHECK(igraph_dqueue_int_push(&mover->unstable_vertices, VECTOR(vertex_order)[i]));
    }
    igraph_vector_int_destroy(&vertex_order);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* Sums the vertex weights and sizes of the start clusters, and records the
 * empty cluster ids and the number of occupied clusters. */
static igraph_error_t leiden_mover_init_clusters(leiden_mover_t *mover, igraph_int_t n) {
    IGRAPH_CHECK(igraph_vector_init(&mover->cluster_out_weights, n));
    if (mover->directed) {
        IGRAPH_CHECK(igraph_vector_init(&mover->cluster_in_weights, n));
    }
    IGRAPH_CHECK(igraph_vector_int_init(&mover->nb_vertices_per_cluster, n));
    for (igraph_int_t i = 0; i < n; i++) {
        const igraph_int_t c = VECTOR(*mover->membership)[i];
        VECTOR(mover->cluster_out_weights)[c] += VECTOR(*mover->vertex_out_weights)[i];
        if (mover->directed) {
            VECTOR(mover->cluster_in_weights)[c] += VECTOR(*mover->vertex_in_weights)[i];
        }
        VECTOR(mover->nb_vertices_per_cluster)[c] += 1;
    }

    IGRAPH_CHECK(igraph_stack_int_init(&mover->empty_clusters, n));
    for (igraph_int_t c = 0; c < n; c++) {
        if (VECTOR(mover->nb_vertices_per_cluster)[c] == 0) {
            IGRAPH_CHECK(igraph_stack_int_push(&mover->empty_clusters, c));
        } else {
            mover->occupied_clusters++;
        }
    }

    IGRAPH_CHECK(leiden_label_index_init(&mover->cluster_index, &mover->cluster_out_weights,
                                         mover->options->resolution < 0.0,
                                         mover->use_cluster_index ? n : 0));
    if (mover->use_cluster_index) {
        IGRAPH_CHECK(leiden_label_index_rebuild(&mover->cluster_index,
                                                &mover->nb_vertices_per_cluster, n));
    }
    return IGRAPH_SUCCESS;
}

/* Prepares local moving of `membership` on `graph`. The caller has
 * zero-initialized `mover` and registered leiden_mover_destroy. */
static igraph_error_t leiden_mover_init(leiden_mover_t *mover,
                                        const igraph_t *graph,
                                        const igraph_inclist_t *edges_per_vertex,
                                        const igraph_vector_t *edge_weights,
                                        const igraph_vector_t *vertex_out_weights,
                                        const igraph_vector_t *vertex_in_weights,
                                        const leiden_options_t *options,
                                        igraph_vector_int_t *membership) {
    const igraph_int_t n = igraph_vcount(graph);

    mover->graph = graph;
    mover->edges_per_vertex = edges_per_vertex;
    mover->edge_weights = edge_weights;
    mover->vertex_out_weights = vertex_out_weights;
    mover->vertex_in_weights = vertex_in_weights;
    mover->options = options;
    mover->membership = membership;
    mover->directed = (vertex_in_weights != NULL);
    mover->count_constrained =
        options->max_total_communities >= 0 || options->n_communities >= 0;
    mover->signed_node_weights = n > 0 &&
        (igraph_vector_min(vertex_out_weights) < 0.0 ||
         (mover->directed && igraph_vector_min(vertex_in_weights) < 0.0));
    mover->use_cluster_index = !mover->directed && options->resolution != 0.0 &&
        (!options->allow_isolation || options->resolution < 0.0 || mover->count_constrained ||
         mover->signed_node_weights);

    IGRAPH_CHECK(leiden_mover_init_queue(mover, n));
    IGRAPH_CHECK(leiden_mover_init_clusters(mover, n));
    IGRAPH_CHECK(igraph_vector_init(&mover->edge_weights_per_cluster, n));
    IGRAPH_CHECK(igraph_bitset_init(&mover->neighbor_cluster_added, n));
    IGRAPH_CHECK(igraph_vector_int_init(&mover->neighbor_clusters, n));
    return IGRAPH_SUCCESS;
}

/* ---- Section 3.2.2  Removing and inserting a vertex ----------------------- */

/* Takes vertex v out of cluster c (its membership entry is left unchanged). */
static igraph_error_t leiden_mover_remove_vertex(leiden_mover_t *mover,
                                                 igraph_int_t v, igraph_int_t c) {
    VECTOR(mover->cluster_out_weights)[c] -= VECTOR(*mover->vertex_out_weights)[v];
    if (mover->directed) {
        VECTOR(mover->cluster_in_weights)[c] -= VECTOR(*mover->vertex_in_weights)[v];
    }
    VECTOR(mover->nb_vertices_per_cluster)[c]--;
    if (VECTOR(mover->nb_vertices_per_cluster)[c] == 0) {
        mover->occupied_clusters--;
        IGRAPH_CHECK(igraph_stack_int_push(&mover->empty_clusters, c));
        if (mover->use_cluster_index) {
            leiden_label_index_remove(&mover->cluster_index, c);
        }
    } else if (mover->use_cluster_index) {
        leiden_label_index_update(&mover->cluster_index, c);
    }
    return IGRAPH_SUCCESS;
}

/* Puts vertex v into cluster c (its membership entry is left unchanged). */
static igraph_error_t leiden_mover_insert_vertex(leiden_mover_t *mover,
                                                 igraph_int_t v, igraph_int_t c) {
    if (VECTOR(mover->nb_vertices_per_cluster)[c] == 0) {
        mover->occupied_clusters++;
    }
    VECTOR(mover->cluster_out_weights)[c] += VECTOR(*mover->vertex_out_weights)[v];
    if (mover->directed) {
        VECTOR(mover->cluster_in_weights)[c] += VECTOR(*mover->vertex_in_weights)[v];
    }
    VECTOR(mover->nb_vertices_per_cluster)[c]++;
    if (mover->use_cluster_index) {
        if (VECTOR(mover->nb_vertices_per_cluster)[c] == 1) {
            IGRAPH_CHECK(leiden_label_index_insert(&mover->cluster_index, c));
        } else {
            leiden_label_index_update(&mover->cluster_index, c);
        }
    }
    if (c == igraph_stack_int_top(&mover->empty_clusters)) {
        igraph_stack_int_pop(&mover->empty_clusters);
    }
    return IGRAPH_SUCCESS;
}

/* ---- Section 3.2.3  Candidate clusters ------------------------------------ */

static void leiden_mover_add_candidate(leiden_mover_t *mover, igraph_int_t c) {
    IGRAPH_BIT_SET(mover->neighbor_cluster_added, c);
    VECTOR(mover->neighbor_clusters)[mover->nb_neigh_clusters++] = c;
}

/* May the visited vertex move to a new, empty cluster? */
static igraph_bool_t leiden_mover_offers_empty_cluster(const leiden_mover_t *mover) {
    const leiden_options_t *options = mover->options;
    return options->allow_isolation && options->n_communities < 0 &&
           (options->max_total_communities < 0 ||
            mover->occupied_clusters < options->max_total_communities);
}

/* Adds the clusters of v's neighbours as candidates and accumulates the
 * edge weight from v to each of them. */
static void leiden_mover_collect_neighbor_clusters(leiden_mover_t *mover, igraph_int_t v,
                                                   const igraph_vector_int_t *edges) {
    const igraph_int_t degree = igraph_vector_int_size(edges);

    for (igraph_int_t i = 0; i < degree; i++) {
        const igraph_int_t e = VECTOR(*edges)[i];
        const igraph_int_t u = IGRAPH_OTHER(mover->graph, e, v);
        if (u != v) {
            const igraph_int_t c = VECTOR(*mover->membership)[u];
            if (!IGRAPH_BIT_TEST(mover->neighbor_cluster_added, c)) {
                leiden_mover_add_candidate(mover, c);
            }
            VECTOR(mover->edge_weights_per_cluster)[c] += VECTOR(*mover->edge_weights)[e];
        }
    }
}

/* The resolution times v's weight: the sign that decides whether omitted
 * clusters can beat an empty one. */
static igraph_real_t leiden_mover_signed_scale(const leiden_mover_t *mover, igraph_int_t v) {
    return mover->directed ?
           mover->options->resolution :
           mover->options->resolution * VECTOR(*mover->vertex_out_weights)[v];
}

/* Does v need an omitted cluster to complete its candidate set? An empty
 * cluster (mass 0) dominates omitted clusters only when gamma * n_v >= 0
 * and all masses are non-negative. Signed node weights can give an omitted
 * cluster positive gain even with positive resolution and isolation enabled.
 * When a count limit withholds the empty cluster, a vertex that was alone in
 * its cluster still has that zero-gain option; otherwise it needs one. */
static igraph_bool_t leiden_mover_needs_omitted_cluster(const leiden_mover_t *mover,
                                                        igraph_int_t v,
                                                        igraph_int_t current_cluster,
                                                        igraph_bool_t empty_offered) {
    return mover->signed_node_weights || !mover->options->allow_isolation ||
           leiden_mover_signed_scale(mover, v) < 0.0 ||
           (mover->count_constrained && !empty_offered &&
            VECTOR(mover->nb_vertices_per_cluster)[current_cluster] > 0);
}

/* Among occupied clusters that are not yet candidates, returns the one that
 * extremizes the omitted gain -gamma * mass(c): the least massive for
 * gamma * weight > 0, the most massive for gamma * weight < 0. When
 * gamma * weight is zero every omitted gain is zero; the first omitted
 * cluster is still returned, because with signed edge weights the current
 * cluster can score below zero. Undirected mass is cluster_out_weights[c];
 * directed mass is vertex_out * cluster_in + vertex_in * cluster_out. Ties
 * prefer the lowest identifier. Returns -1 if there is no such cluster. */
static igraph_int_t leiden_find_omitted_extreme_cluster(
        const igraph_vector_t *cluster_out_weights,
        const igraph_vector_t *cluster_in_weights,
        const igraph_vector_int_t *nb_vertices_per_cluster,
        const igraph_bitset_t *candidate_marker,
        igraph_int_t n_ids,
        igraph_real_t vertex_out_weight,
        igraph_real_t vertex_in_weight,
        igraph_real_t resolution) {
    const igraph_bool_t directed = (cluster_in_weights != NULL);
    const igraph_real_t signed_scale = directed ? resolution : resolution * vertex_out_weight;
    const igraph_bool_t want_min = (signed_scale > 0.0);
    igraph_int_t best = -1;
    igraph_real_t best_mass = 0.0;

    for (igraph_int_t c = 0; c < n_ids; c++) {
        igraph_real_t mass;

        if (VECTOR(*nb_vertices_per_cluster)[c] <= 0) {
            continue;
        }
        if (IGRAPH_BIT_TEST(*candidate_marker, c)) {
            continue;
        }
        if (signed_scale == 0.0) {
            return c;
        }

        if (directed) {
            mass = vertex_out_weight * VECTOR(*cluster_in_weights)[c] +
                   vertex_in_weight * VECTOR(*cluster_out_weights)[c];
        } else {
            mass = VECTOR(*cluster_out_weights)[c];
        }

        if (best < 0 ||
            (want_min ? (mass < best_mass || (mass == best_mass && c < best))
                      : (mass > best_mass || (mass == best_mass && c < best)))) {
            best = c;
            best_mass = mass;
        }
    }

    return best;
}

/* The omitted cluster of v, through the label index when it applies (debug
 * builds check it against the linear scan), otherwise by the scan. */
static igraph_error_t leiden_mover_find_omitted_cluster(leiden_mover_t *mover, igraph_int_t v,
                                                        igraph_int_t *omitted) {
    const igraph_int_t n = igraph_vcount(mover->graph);
    const igraph_real_t resolution = mover->options->resolution;
    const igraph_real_t signed_scale = leiden_mover_signed_scale(mover, v);

    if (mover->use_cluster_index && signed_scale != 0.0 &&
        (signed_scale > 0.0) == (resolution > 0.0)) {
        IGRAPH_CHECK(leiden_label_index_begin(&mover->cluster_index));
        IGRAPH_CHECK(leiden_label_index_next(&mover->cluster_index, NULL,
                                             &mover->neighbor_cluster_added, omitted));
#ifndef NDEBUG
        if (*omitted != leiden_find_omitted_extreme_cluster(
                &mover->cluster_out_weights, NULL, &mover->nb_vertices_per_cluster,
                &mover->neighbor_cluster_added, n, VECTOR(*mover->vertex_out_weights)[v],
                0.0, resolution)) {
            IGRAPH_ERROR("Leiden cluster index disagrees with the "
                         "omitted-cluster scan.", IGRAPH_EINTERNAL);
        }
#endif
    } else {
        *omitted = leiden_find_omitted_extreme_cluster(
            &mover->cluster_out_weights,
            mover->directed ? &mover->cluster_in_weights : NULL,
            &mover->nb_vertices_per_cluster,
            &mover->neighbor_cluster_added,
            n,
            VECTOR(*mover->vertex_out_weights)[v],
            mover->directed ? VECTOR(*mover->vertex_in_weights)[v] : 0.0,
            resolution);
    }
    return IGRAPH_SUCCESS;
}

/* Builds the candidate list of v in this order: the empty cluster (if
 * offered), the neighbour clusters, the omitted cluster (if needed). */
static igraph_error_t leiden_mover_collect_candidates(leiden_mover_t *mover, igraph_int_t v,
                                                      igraph_int_t current_cluster,
                                                      const igraph_vector_int_t *edges) {
    const igraph_bool_t empty_offered = leiden_mover_offers_empty_cluster(mover);

    mover->nb_neigh_clusters = 0;
    if (empty_offered) {
        leiden_mover_add_candidate(mover, igraph_stack_int_top(&mover->empty_clusters));
    }
    leiden_mover_collect_neighbor_clusters(mover, v, edges);
    if (leiden_mover_needs_omitted_cluster(mover, v, current_cluster, empty_offered)) {
        igraph_int_t omitted;
        IGRAPH_CHECK(leiden_mover_find_omitted_cluster(mover, v, &omitted));
        if (omitted >= 0) {
            leiden_mover_add_candidate(mover, omitted);
        }
    }
    return IGRAPH_SUCCESS;
}

/* Clears the per-visit candidate scratch. */
static void leiden_mover_clear_candidates(leiden_mover_t *mover) {
    for (igraph_int_t i = 0; i < mover->nb_neigh_clusters; i++) {
        const igraph_int_t c = VECTOR(mover->neighbor_clusters)[i];
        VECTOR(mover->edge_weights_per_cluster)[c] = 0.0;
        IGRAPH_BIT_CLEAR(mover->neighbor_cluster_added, c);
    }
}

/* ---- Section 3.2.4  Choosing the best cluster ----------------------------- */

/* Gain of keeping v in its current cluster c (v already removed from c).
 * The directed penalty lists its two terms in the opposite order from the
 * candidate gain below; both orders are kept exactly as released, because
 * floating-point contraction makes them differ in the last bit. */
static igraph_real_t leiden_mover_gain_of_current(const leiden_mover_t *mover,
                                                  igraph_int_t v, igraph_int_t c) {
    const igraph_real_t resolution = mover->options->resolution;
    igraph_real_t diff = VECTOR(mover->edge_weights_per_cluster)[c];

    if (mover->directed) {
        diff -=
            (VECTOR(*mover->vertex_in_weights)[v]  * VECTOR(mover->cluster_out_weights)[c] +
             VECTOR(*mover->vertex_out_weights)[v] * VECTOR(mover->cluster_in_weights)[c]) * resolution;
    } else {
        diff -= VECTOR(*mover->vertex_out_weights)[v] * VECTOR(mover->cluster_out_weights)[c] * resolution;
    }
    return diff;
}

/* Gain of moving v into candidate cluster c. */
static igraph_real_t leiden_mover_gain_of_candidate(const leiden_mover_t *mover,
                                                    igraph_int_t v, igraph_int_t c) {
    const igraph_real_t resolution = mover->options->resolution;
    igraph_real_t diff = VECTOR(mover->edge_weights_per_cluster)[c];

    if (mover->directed) {
        diff -= (VECTOR(*mover->vertex_out_weights)[v] * VECTOR(mover->cluster_in_weights)[c] +
                 VECTOR(*mover->vertex_in_weights)[v]  * VECTOR(mover->cluster_out_weights)[c]) * resolution;
    } else {
        diff -= VECTOR(*mover->vertex_out_weights)[v] * VECTOR(mover->cluster_out_weights)[c] * resolution;
    }
    return diff;
}

/* The candidate with the strictly largest gain, or the current cluster if
 * none improves on it. Candidates are compared in list order, so the first
 * of several equal gains wins. */
static igraph_int_t leiden_mover_best_cluster(const leiden_mover_t *mover,
                                              igraph_int_t v, igraph_int_t current_cluster) {
    igraph_int_t best_cluster = current_cluster;
    igraph_real_t max_diff = leiden_mover_gain_of_current(mover, v, current_cluster);

    for (igraph_int_t i = 0; i < mover->nb_neigh_clusters; i++) {
        const igraph_int_t c = VECTOR(mover->neighbor_clusters)[i];
        const igraph_real_t diff = leiden_mover_gain_of_candidate(mover, v, c);
        /* Only strictly improving moves; this is what makes the loop end. */
        if (mover->options->tolerant ? leiden_is_improvement(diff, max_diff)
                                     : diff > max_diff) {
            best_cluster = c;
            max_diff = diff;
        }
    }

    /* An exact community count forbids emptying a cluster: the last vertex
     * of a cluster keeps it. */
    if (mover->options->n_communities >= 0 &&
        VECTOR(mover->nb_vertices_per_cluster)[current_cluster] == 0) {
        best_cluster = current_cluster;
    }
    return best_cluster;
}

/* ---- Section 3.2.5  The queue loop ---------------------------------------- */

/* Queues the stable neighbours of v that are not in v's new cluster. */
static igraph_error_t leiden_mover_requeue_neighbors(leiden_mover_t *mover, igraph_int_t v,
                                                     const igraph_vector_int_t *edges,
                                                     igraph_int_t new_cluster) {
    const igraph_int_t degree = igraph_vector_int_size(edges);

    for (igraph_int_t i = 0; i < degree; i++) {
        const igraph_int_t e = VECTOR(*edges)[i];
        const igraph_int_t u = IGRAPH_OTHER(mover->graph, e, v);
        if (IGRAPH_BIT_TEST(mover->vertex_is_stable, u) &&
            VECTOR(*mover->membership)[u] != new_cluster) {
            IGRAPH_CHECK(igraph_dqueue_int_push(&mover->unstable_vertices, u));
            IGRAPH_BIT_CLEAR(mover->vertex_is_stable, u);
        }
    }
    return IGRAPH_SUCCESS;
}

/* Visits vertex v: moves it to its best cluster and marks it stable. */
static igraph_error_t leiden_mover_visit(leiden_mover_t *mover, igraph_int_t v,
                                         igraph_bool_t *changed) {
    const igraph_int_t current_cluster = VECTOR(*mover->membership)[v];
    const igraph_vector_int_t *edges = igraph_inclist_get(mover->edges_per_vertex, v);
    igraph_int_t best_cluster;

    IGRAPH_CHECK(leiden_mover_remove_vertex(mover, v, current_cluster));
    IGRAPH_CHECK(leiden_mover_collect_candidates(mover, v, current_cluster, edges));
    best_cluster = leiden_mover_best_cluster(mover, v, current_cluster);
    leiden_mover_clear_candidates(mover);
    IGRAPH_CHECK(leiden_mover_insert_vertex(mover, v, best_cluster));

    IGRAPH_BIT_SET(mover->vertex_is_stable, v);
    if (best_cluster != current_cluster) {
        *changed = true;
        VECTOR(*mover->membership)[v] = best_cluster;
        IGRAPH_CHECK(leiden_mover_requeue_neighbors(mover, v, edges, best_cluster));
    }
    return IGRAPH_SUCCESS;
}

/* Pops and visits vertices until the queue is empty (or, in tolerant mode,
 * until the progress ceiling is reached). */
static igraph_error_t leiden_mover_run(leiden_mover_t *mover, igraph_bool_t *changed) {
    const igraph_int_t progress_ceiling =
        leiden_progress_ceiling(igraph_vcount(mover->graph), 1);

    while (!igraph_dqueue_int_empty(&mover->unstable_vertices)) {
        if (mover->options->tolerant && ++mover->queue_pops > progress_ceiling) {
            break;
        }
        IGRAPH_CHECK(leiden_mover_visit(mover, igraph_dqueue_int_pop(&mover->unstable_vertices),
                                        changed));
        IGRAPH_CHECK(leiden_check_interruption(&mover->interruption_counter, 1 << 14));
    }
    return IGRAPH_SUCCESS;
}

/* Local moving (phase 1). Improves `membership` in place, renumbers it
 * consecutively, reports the number of clusters, and sets *changed if any
 * vertex moved. */
static igraph_error_t leiden_fastmove_vertices(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_vertex,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        const leiden_options_t *options,
        igraph_int_t *nb_clusters,
        igraph_vector_int_t *membership,
        igraph_bool_t *changed) {
    leiden_mover_t mover = { .graph = NULL };

    IGRAPH_FINALLY(leiden_mover_destroy, &mover);
    IGRAPH_CHECK(leiden_mover_init(&mover, graph, edges_per_vertex, edge_weights,
                                   vertex_out_weights, vertex_in_weights, options, membership));
    IGRAPH_CHECK(leiden_mover_run(&mover, changed));

    IGRAPH_CHECK(igraph_reindex_membership(membership, NULL, nb_clusters));
    if ((options->max_total_communities >= 0 && *nb_clusters > options->max_total_communities) ||
        (options->n_communities >= 0 && *nb_clusters != options->n_communities)) {
        IGRAPH_ERROR("Leiden local moving violated a community-count constraint.",
                     IGRAPH_EINTERNAL);
    }

    leiden_mover_destroy(&mover);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}


/* -----------------------------------------------------------------------------
 * Section 3.3  Refinement
 * -----------------------------------------------------------------------------
 *
 * Refines one cluster, given as `vertex_subset` (the vertices i with
 * membership[i] == cluster_subset). Its vertices start as singletons in
 * `refined_membership`. Each vertex is examined once, in random order; a
 * vertex that is still a singleton and is well connected to the rest of the
 * subset may join a neighbouring refined cluster that is itself well
 * connected. Instead of the best such cluster, one is drawn at random among
 * those that do not decrease the quality, with probability proportional to
 * exp(gain / beta): beta -> 0 approaches the greedy choice, beta -> infinity
 * a uniform choice. Merged clusters never split again in this pass.
 *
 * Refined cluster ids of different subsets must not collide: after merging,
 * leiden_clean_refined_membership renumbers the subset's refined clusters
 * from *nb_refined_clusters upwards and advances the counter.
 */

/* ---- Section 3.3.1  Workspace --------------------------------------------- */

typedef struct {
    /* Inputs, borrowed from the caller. */
    const igraph_t *graph;
    const igraph_inclist_t *edges_per_vertex;
    const igraph_vector_t *edge_weights;
    const igraph_vector_t *vertex_out_weights;
    const igraph_vector_t *vertex_in_weights;    /* NULL for undirected graphs */
    const igraph_vector_int_t *membership;       /* the unrefined partition */
    igraph_int_t cluster_subset;                 /* the cluster being refined */
    const leiden_options_t *options;
    igraph_vector_int_t *refined_membership;
    igraph_bool_t directed;

    /* Refined clusters, indexed 0 .. |subset| - 1. */
    igraph_real_t total_vertex_out_weight;
    igraph_real_t total_vertex_in_weight;
    igraph_vector_t cluster_out_weights;
    igraph_vector_t cluster_in_weights;          /* directed graphs only */
    /* Weight of edges from the refined cluster to the rest of the subset. */
    igraph_vector_t external_edge_weight_per_cluster_in_subset;
    igraph_bitset_t non_singleton_cluster;
    igraph_vector_int_t vertex_order;

    /* Candidates of the examined vertex. */
    igraph_vector_t edge_weights_per_cluster;
    igraph_bitset_t neighbor_cluster_added;
    igraph_vector_int_t neighbor_clusters;
    igraph_int_t nb_neigh_clusters;
    igraph_vector_t cum_trans_diff;              /* running sums of exp(gain / beta) */
} leiden_refiner_t;

static void leiden_refiner_destroy(leiden_refiner_t *refiner) {
    igraph_vector_destroy(&refiner->cum_trans_diff);
    igraph_vector_int_destroy(&refiner->neighbor_clusters);
    igraph_bitset_destroy(&refiner->neighbor_cluster_added);
    igraph_vector_destroy(&refiner->edge_weights_per_cluster);
    igraph_bitset_destroy(&refiner->non_singleton_cluster);
    igraph_vector_int_destroy(&refiner->vertex_order);
    igraph_vector_destroy(&refiner->external_edge_weight_per_cluster_in_subset);
    igraph_vector_destroy(&refiner->cluster_in_weights);
    igraph_vector_destroy(&refiner->cluster_out_weights);
}

/* Puts every vertex of the subset into its own refined cluster and records
 * cluster weights, total weights and each vertex's edge weight to the rest
 * of the subset. */
static void leiden_refiner_start_singletons(leiden_refiner_t *refiner,
                                            const igraph_vector_int_t *vertex_subset) {
    const igraph_int_t n = igraph_vector_int_size(vertex_subset);

    for (igraph_int_t i = 0; i < n; i++) {
        const igraph_int_t v = VECTOR(*vertex_subset)[i];
        const igraph_vector_int_t *edges = igraph_inclist_get(refiner->edges_per_vertex, v);
        const igraph_int_t degree = igraph_vector_int_size(edges);

        VECTOR(*refiner->refined_membership)[v] = i;
        VECTOR(refiner->cluster_out_weights)[i] += VECTOR(*refiner->vertex_out_weights)[v];
        refiner->total_vertex_out_weight += VECTOR(*refiner->vertex_out_weights)[v];
        if (refiner->directed) {
            VECTOR(refiner->cluster_in_weights)[i] += VECTOR(*refiner->vertex_in_weights)[v];
            refiner->total_vertex_in_weight += VECTOR(*refiner->vertex_in_weights)[v];
        }
        for (igraph_int_t j = 0; j < degree; j++) {
            const igraph_int_t e = VECTOR(*edges)[j];
            const igraph_int_t u = IGRAPH_OTHER(refiner->graph, e, v);
            if (u != v && VECTOR(*refiner->membership)[u] == refiner->cluster_subset) {
                VECTOR(refiner->external_edge_weight_per_cluster_in_subset)[i] +=
                    VECTOR(*refiner->edge_weights)[e];
            }
        }
    }
}

/* Prepares the refinement of one cluster. The caller has zero-initialized
 * `refiner` and registered leiden_refiner_destroy. */
static igraph_error_t leiden_refiner_init(leiden_refiner_t *refiner,
                                          const igraph_t *graph,
                                          const igraph_inclist_t *edges_per_vertex,
                                          const igraph_vector_t *edge_weights,
                                          const igraph_vector_t *vertex_out_weights,
                                          const igraph_vector_t *vertex_in_weights,
                                          const igraph_vector_int_t *vertex_subset,
                                          const igraph_vector_int_t *membership,
                                          igraph_int_t cluster_subset,
                                          const leiden_options_t *options,
                                          igraph_vector_int_t *refined_membership) {
    const igraph_int_t n = igraph_vector_int_size(vertex_subset);

    refiner->graph = graph;
    refiner->edges_per_vertex = edges_per_vertex;
    refiner->edge_weights = edge_weights;
    refiner->vertex_out_weights = vertex_out_weights;
    refiner->vertex_in_weights = vertex_in_weights;
    refiner->membership = membership;
    refiner->cluster_subset = cluster_subset;
    refiner->options = options;
    refiner->refined_membership = refined_membership;
    refiner->directed = (vertex_in_weights != NULL);

    IGRAPH_CHECK(igraph_vector_init(&refiner->cluster_out_weights, n));
    if (refiner->directed) {
        IGRAPH_CHECK(igraph_vector_init(&refiner->cluster_in_weights, n));
    }
    IGRAPH_CHECK(igraph_vector_init(&refiner->external_edge_weight_per_cluster_in_subset, n));
    leiden_refiner_start_singletons(refiner, vertex_subset);

    /* The random visiting order. */
    IGRAPH_CHECK(igraph_vector_int_init_copy(&refiner->vertex_order, vertex_subset));
    igraph_vector_int_shuffle(&refiner->vertex_order);

    IGRAPH_CHECK(igraph_bitset_init(&refiner->non_singleton_cluster, n));
    IGRAPH_CHECK(igraph_vector_init(&refiner->edge_weights_per_cluster, n));
    IGRAPH_CHECK(igraph_bitset_init(&refiner->neighbor_cluster_added, n));
    IGRAPH_CHECK(igraph_vector_int_init(&refiner->neighbor_clusters, n));
    IGRAPH_CHECK(igraph_vector_init(&refiner->cum_trans_diff, n));
    return IGRAPH_SUCCESS;
}

/* ---- Section 3.3.2  Well-connectedness ------------------------------------ */

/* The product of refined cluster c's weight with the weight of the rest of
 * the subset (out/in combined for directed graphs). */
static igraph_real_t leiden_refiner_weight_product(const leiden_refiner_t *refiner,
                                                   igraph_int_t c) {
    if (refiner->directed) {
        return VECTOR(refiner->cluster_out_weights)[c] *
               (refiner->total_vertex_in_weight - VECTOR(refiner->cluster_in_weights)[c]) +
               VECTOR(refiner->cluster_in_weights)[c] *
               (refiner->total_vertex_out_weight - VECTOR(refiner->cluster_out_weights)[c]);
    }
    return VECTOR(refiner->cluster_out_weights)[c] *
           (refiner->total_vertex_out_weight - VECTOR(refiner->cluster_out_weights)[c]);
}

/* Is refined cluster c well connected to the rest of the subset? */
static igraph_bool_t leiden_refiner_is_well_connected(const leiden_refiner_t *refiner,
                                                      igraph_int_t c) {
    const igraph_real_t vertex_weight_prod = leiden_refiner_weight_product(refiner, c);
    return VECTOR(refiner->external_edge_weight_per_cluster_in_subset)[c] >=
           vertex_weight_prod * refiner->options->resolution;
}

/* ---- Section 3.3.3  Randomized merge of one vertex ------------------------ */

/* Lists v's own (singleton) refined cluster and the refined clusters of its
 * neighbours inside the subset, accumulating the edge weight to each. */
static void leiden_refiner_collect_neighbors(leiden_refiner_t *refiner, igraph_int_t v,
                                             igraph_int_t current_cluster,
                                             const igraph_vector_int_t *edges) {
    const igraph_int_t degree = igraph_vector_int_size(edges);

    VECTOR(refiner->neighbor_clusters)[0] = current_cluster;
    IGRAPH_BIT_SET(refiner->neighbor_cluster_added, current_cluster);
    refiner->nb_neigh_clusters = 1;
    for (igraph_int_t j = 0; j < degree; j++) {
        const igraph_int_t e = VECTOR(*edges)[j];
        const igraph_int_t u = IGRAPH_OTHER(refiner->graph, e, v);
        if (u != v && VECTOR(*refiner->membership)[u] == refiner->cluster_subset) {
            const igraph_int_t c = VECTOR(*refiner->refined_membership)[u];
            if (!IGRAPH_BIT_TEST(refiner->neighbor_cluster_added, c)) {
                IGRAPH_BIT_SET(refiner->neighbor_cluster_added, c);
                VECTOR(refiner->neighbor_clusters)[refiner->nb_neigh_clusters++] = c;
            }
            VECTOR(refiner->edge_weights_per_cluster)[c] += VECTOR(*refiner->edge_weights)[e];
        }
    }
}

/* Gain of merging v into refined cluster c. */
static igraph_real_t leiden_refiner_gain(const leiden_refiner_t *refiner,
                                         igraph_int_t v, igraph_int_t c) {
    const igraph_real_t resolution = refiner->options->resolution;
    igraph_real_t diff = VECTOR(refiner->edge_weights_per_cluster)[c];

    if (refiner->directed) {
        diff -= (VECTOR(*refiner->vertex_out_weights)[v] * VECTOR(refiner->cluster_in_weights)[c] +
                 VECTOR(*refiner->vertex_in_weights)[v] * VECTOR(refiner->cluster_out_weights)[c]) * resolution;
    } else {
        diff -= VECTOR(*refiner->vertex_out_weights)[v] * VECTOR(refiner->cluster_out_weights)[c] * resolution;
    }
    return diff;
}

/* Scores every listed cluster that is well connected: records the best gain
 * and the running sums of exp(gain / beta) over non-negative gains, then
 * clears the candidate scratch. Returns the total of those sums. */
static igraph_real_t leiden_refiner_score_candidates(leiden_refiner_t *refiner, igraph_int_t v,
                                                     igraph_int_t current_cluster,
                                                     igraph_int_t *best_cluster) {
    igraph_real_t max_diff = 0.0, total_cum_trans_diff = 0.0;

    *best_cluster = current_cluster;
    for (igraph_int_t j = 0; j < refiner->nb_neigh_clusters; j++) {
        const igraph_int_t c = VECTOR(refiner->neighbor_clusters)[j];

        if (leiden_refiner_is_well_connected(refiner, c)) {
            const igraph_real_t diff = leiden_refiner_gain(refiner, v, c);
            if (diff > max_diff) {
                *best_cluster = c;
                max_diff = diff;
            }
            if (diff >= 0) {
                total_cum_trans_diff += exp(diff / refiner->options->beta);
            }
        }

        VECTOR(refiner->cum_trans_diff)[j] = total_cum_trans_diff;
        VECTOR(refiner->edge_weights_per_cluster)[c] = 0.0;
        IGRAPH_BIT_CLEAR(refiner->neighbor_cluster_added, c);
    }
    return total_cum_trans_diff;
}

/* Draws a cluster with probability proportional to exp(gain / beta); falls
 * back to the best cluster when the weights overflow. */
static igraph_int_t leiden_refiner_draw_cluster(const leiden_refiner_t *refiner,
                                                igraph_real_t total_cum_trans_diff,
                                                igraph_int_t best_cluster) {
    if (total_cum_trans_diff < IGRAPH_INFINITY) {
        const igraph_real_t r = RNG_UNIF(0, total_cum_trans_diff);
        igraph_int_t chosen_idx;
        igraph_vector_binsearch_slice(&refiner->cum_trans_diff, r, &chosen_idx, 0,
                                      refiner->nb_neigh_clusters);
        return VECTOR(refiner->neighbor_clusters)[chosen_idx];
    }
    return best_cluster;
}

/* Moves v into refined cluster `chosen` and updates the chosen cluster's
 * weight to the rest of the subset. */
static void leiden_refiner_join(leiden_refiner_t *refiner, igraph_int_t v,
                                igraph_int_t current_cluster, igraph_int_t chosen,
                                const igraph_vector_int_t *edges) {
    const igraph_int_t degree = igraph_vector_int_size(edges);

    VECTOR(refiner->cluster_out_weights)[chosen] += VECTOR(*refiner->vertex_out_weights)[v];
    if (refiner->directed) {
        VECTOR(refiner->cluster_in_weights)[chosen] += VECTOR(*refiner->vertex_in_weights)[v];
    }
    for (igraph_int_t j = 0; j < degree; j++) {
        const igraph_int_t e = VECTOR(*edges)[j];
        const igraph_int_t u = IGRAPH_OTHER(refiner->graph, e, v);
        if (VECTOR(*refiner->membership)[u] == refiner->cluster_subset) {
            if (VECTOR(*refiner->refined_membership)[u] == chosen) {
                VECTOR(refiner->external_edge_weight_per_cluster_in_subset)[chosen] -=
                    VECTOR(*refiner->edge_weights)[e];
            } else {
                VECTOR(refiner->external_edge_weight_per_cluster_in_subset)[chosen] +=
                    VECTOR(*refiner->edge_weights)[e];
            }
        }
    }
    if (chosen != current_cluster) {
        VECTOR(*refiner->refined_membership)[v] = chosen;
        IGRAPH_BIT_SET(refiner->non_singleton_cluster, chosen);
    }
}

/* Examines vertex v: if it is still a well-connected singleton, detaches it
 * and merges it into a randomly drawn refined cluster. */
static void leiden_refiner_visit(leiden_refiner_t *refiner, igraph_int_t v) {
    const igraph_int_t current_cluster = VECTOR(*refiner->refined_membership)[v];
    const igraph_vector_int_t *edges;
    igraph_int_t best_cluster;
    igraph_real_t total;

    if (IGRAPH_BIT_TEST(refiner->non_singleton_cluster, current_cluster) ||
        !leiden_refiner_is_well_connected(refiner, current_cluster)) {
        return;
    }

    /* Detach v: its refined cluster is a singleton by definition. */
    VECTOR(refiner->cluster_out_weights)[current_cluster] = 0.0;
    if (refiner->directed) {
        VECTOR(refiner->cluster_in_weights)[current_cluster] = 0.0;
    }

    edges = igraph_inclist_get(refiner->edges_per_vertex, v);
    leiden_refiner_collect_neighbors(refiner, v, current_cluster, edges);
    total = leiden_refiner_score_candidates(refiner, v, current_cluster, &best_cluster);
    leiden_refiner_join(refiner, v, current_cluster,
                        leiden_refiner_draw_cluster(refiner, total, best_cluster), edges);
}

/* ---- Section 3.3.4  Renumbering refined clusters -------------------------- */

/* Renumbers the refined clusters of the vertices in `vertex_subset`
 * consecutively from *nb_refined_clusters, in order of first appearance,
 * and advances *nb_refined_clusters past them. */
static igraph_error_t leiden_clean_refined_membership(
        const igraph_vector_int_t *vertex_subset,
        igraph_vector_int_t *refined_membership,
        igraph_int_t *nb_refined_clusters) {
    const igraph_int_t n = igraph_vector_int_size(vertex_subset);
    igraph_vector_int_t new_cluster;

    IGRAPH_VECTOR_INT_INIT_FINALLY(&new_cluster, n);

    /* Store the new cluster + 1, so that 0 means "not assigned yet". */
    *nb_refined_clusters += 1;
    for (igraph_int_t i = 0; i < n; i++) {
        const igraph_int_t v = VECTOR(*vertex_subset)[i];
        const igraph_int_t c = VECTOR(*refined_membership)[v];
        if (VECTOR(new_cluster)[c] == 0) {
            VECTOR(new_cluster)[c] = *nb_refined_clusters;
            *nb_refined_clusters += 1;
        }
    }
    for (igraph_int_t i = 0; i < n; i++) {
        const igraph_int_t v = VECTOR(*vertex_subset)[i];
        const igraph_int_t c = VECTOR(*refined_membership)[v];
        VECTOR(*refined_membership)[v] = VECTOR(new_cluster)[c] - 1;
    }
    *nb_refined_clusters -= 1;

    igraph_vector_int_destroy(&new_cluster);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* Refines cluster `cluster_subset` (phase 2). */
static igraph_error_t leiden_merge_vertices(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_vertex,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        const igraph_vector_int_t *vertex_subset,
        const igraph_vector_int_t *membership,
        igraph_int_t cluster_subset,
        const leiden_options_t *options,
        igraph_int_t *nb_refined_clusters,
        igraph_vector_int_t *refined_membership) {
    leiden_refiner_t refiner = { .graph = NULL };

    IGRAPH_FINALLY(leiden_refiner_destroy, &refiner);
    IGRAPH_CHECK(leiden_refiner_init(&refiner, graph, edges_per_vertex, edge_weights,
                                     vertex_out_weights, vertex_in_weights, vertex_subset,
                                     membership, cluster_subset, options, refined_membership));
    for (igraph_int_t i = 0; i < igraph_vector_int_size(vertex_subset); i++) {
        leiden_refiner_visit(&refiner, VECTOR(refiner.vertex_order)[i]);
    }
    IGRAPH_CHECK(leiden_clean_refined_membership(vertex_subset, refined_membership,
                                                 nb_refined_clusters));
    leiden_refiner_destroy(&refiner);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 3.4  Aggregation
 * -----------------------------------------------------------------------------
 *
 * Builds the next level: one vertex per refined cluster, one edge per pair of
 * refined clusters joined by at least one edge (weight: their total edge
 * weight), vertex weights summed, and each aggregate vertex placed in the
 * unrefined cluster of its members:
 *
 *     aggregated_membership[refined_membership[v]] = membership[v].
 *
 * Edges inside a refined cluster are dropped: they move together with their
 * aggregate vertex, so they change no gain at coarser levels (the final
 * quality is always computed on the original graph).
 */

typedef struct {
    igraph_vector_int_list_t refined_clusters;   /* members of each refined cluster */
    igraph_vector_int_t aggregated_edges;
    igraph_vector_t edge_weight_to_cluster;
    igraph_bitset_t neighbor_cluster_added;
    igraph_vector_int_t neighbor_clusters;
    igraph_int_t nb_neigh_clusters;
} leiden_aggregator_t;

static void leiden_aggregator_destroy(leiden_aggregator_t *aggregator) {
    igraph_vector_int_destroy(&aggregator->neighbor_clusters);
    igraph_bitset_destroy(&aggregator->neighbor_cluster_added);
    igraph_vector_destroy(&aggregator->edge_weight_to_cluster);
    igraph_vector_int_destroy(&aggregator->aggregated_edges);
    igraph_vector_int_list_destroy(&aggregator->refined_clusters);
}

/* Appends each vertex i to clusters[membership[i]]; the list must already be
 * long enough and its vectors empty. */
static igraph_error_t leiden_get_clusters(const igraph_vector_int_t *membership,
                                          igraph_vector_int_list_t *clusters) {
    const igraph_int_t n = igraph_vector_int_size(membership);

    for (igraph_int_t i = 0; i < n; i++) {
        igraph_vector_int_t *cluster =
            igraph_vector_int_list_get_ptr(clusters, VECTOR(*membership)[i]);
        IGRAPH_CHECK(igraph_vector_int_push_back(cluster, i));
    }
    return IGRAPH_SUCCESS;
}

/* Sums the vertex weights of refined cluster c and the weights of its edges
 * to refined clusters with a larger id (each pair is emitted once). Returns
 * the last member of c. */
static igraph_int_t leiden_aggregate_collect(leiden_aggregator_t *aggregator,
                                             const igraph_t *graph,
                                             const igraph_inclist_t *edges_per_vertex,
                                             const igraph_vector_t *edge_weights,
                                             const igraph_vector_t *vertex_out_weights,
                                             const igraph_vector_t *vertex_in_weights,
                                             const igraph_vector_int_t *refined_membership,
                                             igraph_int_t c,
                                             igraph_vector_t *aggregated_vertex_out_weights,
                                             igraph_vector_t *aggregated_vertex_in_weights) {
    const igraph_vector_int_t *refined_cluster =
        igraph_vector_int_list_get_ptr(&aggregator->refined_clusters, c);
    const igraph_int_t n_c = igraph_vector_int_size(refined_cluster);
    igraph_int_t v = -1;

    VECTOR(*aggregated_vertex_out_weights)[c] = 0.0;
    if (vertex_in_weights) {
        VECTOR(*aggregated_vertex_in_weights)[c] = 0.0;
    }
    aggregator->nb_neigh_clusters = 0;
    for (igraph_int_t i = 0; i < n_c; i++) {
        const igraph_vector_int_t *incident_edges;
        igraph_int_t degree;

        v = VECTOR(*refined_cluster)[i];
        incident_edges = igraph_inclist_get(edges_per_vertex, v);
        degree = igraph_vector_int_size(incident_edges);
        for (igraph_int_t j = 0; j < degree; j++) {
            const igraph_int_t e = VECTOR(*incident_edges)[j];
            const igraph_int_t u = IGRAPH_OTHER(graph, e, v);
            const igraph_int_t c2 = VECTOR(*refined_membership)[u];
            if (c2 > c) {
                if (!IGRAPH_BIT_TEST(aggregator->neighbor_cluster_added, c2)) {
                    IGRAPH_BIT_SET(aggregator->neighbor_cluster_added, c2);
                    VECTOR(aggregator->neighbor_clusters)[aggregator->nb_neigh_clusters++] = c2;
                }
                VECTOR(aggregator->edge_weight_to_cluster)[c2] += VECTOR(*edge_weights)[e];
            }
        }
        VECTOR(*aggregated_vertex_out_weights)[c] += VECTOR(*vertex_out_weights)[v];
        if (vertex_in_weights) {
            VECTOR(*aggregated_vertex_in_weights)[c] += VECTOR(*vertex_in_weights)[v];
        }
    }
    return v;
}

/* Emits the edges from refined cluster c collected above and clears the
 * scratch. */
static igraph_error_t leiden_aggregate_emit_edges(leiden_aggregator_t *aggregator,
                                                  igraph_int_t c,
                                                  igraph_vector_t *aggregated_edge_weights) {
    for (igraph_int_t i = 0; i < aggregator->nb_neigh_clusters; i++) {
        const igraph_int_t c2 = VECTOR(aggregator->neighbor_clusters)[i];
        IGRAPH_CHECK(igraph_vector_int_push_back(&aggregator->aggregated_edges, c));
        IGRAPH_CHECK(igraph_vector_int_push_back(&aggregator->aggregated_edges, c2));
        IGRAPH_CHECK(igraph_vector_push_back(aggregated_edge_weights,
                                             VECTOR(aggregator->edge_weight_to_cluster)[c2]));
        VECTOR(aggregator->edge_weight_to_cluster)[c2] = 0.0;
        IGRAPH_BIT_CLEAR(aggregator->neighbor_cluster_added, c2);
    }
    return IGRAPH_SUCCESS;
}

/* Replaces *aggregated_graph (which must be a valid graph) by a new graph on
 * `nb_vertices` vertices with the collected edges. The old graph is
 * destroyed only after the new one exists, so a failure leaves it valid. */
static igraph_error_t leiden_aggregate_replace_graph(leiden_aggregator_t *aggregator,
                                                     igraph_int_t nb_vertices,
                                                     igraph_bool_t directed,
                                                     igraph_t *aggregated_graph) {
    igraph_t new_graph;

    IGRAPH_CHECK(igraph_create(&new_graph, &aggregator->aggregated_edges, nb_vertices, directed));
    igraph_destroy(aggregated_graph);
    *aggregated_graph = new_graph;
    return IGRAPH_SUCCESS;
}

/* Aggregation (phase 3). The output vectors must be initialized; they are
 * resized here. */
static igraph_error_t leiden_aggregate(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_vertex,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        const igraph_vector_int_t *membership,
        const igraph_vector_int_t *refined_membership,
        igraph_int_t nb_refined_clusters,
        igraph_t *aggregated_graph,
        igraph_vector_t *aggregated_edge_weights,
        igraph_vector_t *aggregated_vertex_out_weights,
        igraph_vector_t *aggregated_vertex_in_weights,
        igraph_vector_int_t *aggregated_membership) {
    const igraph_bool_t directed = (vertex_in_weights != NULL);
    leiden_aggregator_t aggregator = { .nb_neigh_clusters = 0 };

    IGRAPH_FINALLY(leiden_aggregator_destroy, &aggregator);
    IGRAPH_CHECK(igraph_vector_int_list_init(&aggregator.refined_clusters, nb_refined_clusters));
    IGRAPH_CHECK(leiden_get_clusters(refined_membership, &aggregator.refined_clusters));
    IGRAPH_CHECK(igraph_vector_int_init(&aggregator.aggregated_edges, 0));

    igraph_vector_clear(aggregated_edge_weights);
    IGRAPH_CHECK(igraph_vector_resize(aggregated_vertex_out_weights, nb_refined_clusters));
    if (directed) {
        IGRAPH_CHECK(igraph_vector_resize(aggregated_vertex_in_weights, nb_refined_clusters));
    }
    IGRAPH_CHECK(igraph_vector_int_resize(aggregated_membership, nb_refined_clusters));

    IGRAPH_CHECK(igraph_vector_init(&aggregator.edge_weight_to_cluster, nb_refined_clusters));
    IGRAPH_CHECK(igraph_bitset_init(&aggregator.neighbor_cluster_added, nb_refined_clusters));
    IGRAPH_CHECK(igraph_vector_int_init(&aggregator.neighbor_clusters, nb_refined_clusters));

    for (igraph_int_t c = 0; c < nb_refined_clusters; c++) {
        const igraph_int_t last_member = leiden_aggregate_collect(
            &aggregator, graph, edges_per_vertex, edge_weights, vertex_out_weights,
            vertex_in_weights, refined_membership, c, aggregated_vertex_out_weights,
            aggregated_vertex_in_weights);
        IGRAPH_CHECK(leiden_aggregate_emit_edges(&aggregator, c, aggregated_edge_weights));
        VECTOR(*aggregated_membership)[c] = VECTOR(*membership)[last_member];
    }

    IGRAPH_CHECK(leiden_aggregate_replace_graph(&aggregator, nb_refined_clusters, directed,
                                                aggregated_graph));
    leiden_aggregator_destroy(&aggregator);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 3.5  Quality
 * -----------------------------------------------------------------------------
 *
 *     Q = 1/2m sum_ij (A_ij - gamma n_i n_j) delta(s_i, s_j)      (undirected)
 *     Q = 1/m  sum_ij (A_ij - gamma n^out_i n^in_j) delta(s_i, s_j) (directed)
 *
 * computed per cluster as 1/2m sum_c (e_c - gamma N_c^2), where e_c is the
 * internal edge weight (counted twice if undirected) and N_c the summed
 * vertex weight. Unit vertex weights give the CPM; n_i = k_i with gamma / 2m
 * gives modularity.
 */

/* Adds the internal edge weight to *quality (times the direction
 * multiplier) and returns the total edge weight. */
static igraph_real_t leiden_quality_add_internal_weight(const igraph_t *graph,
                                                        const igraph_vector_t *edge_weights,
                                                        const igraph_vector_int_t *membership,
                                                        igraph_real_t directed_multiplier,
                                                        igraph_real_t *quality) {
    const igraph_int_t ecount = igraph_ecount(graph);
    igraph_real_t total_edge_weight = 0.0;

    for (igraph_int_t e = 0; e < ecount; e++) {
        const igraph_int_t from = IGRAPH_FROM(graph, e);
        const igraph_int_t to = IGRAPH_TO(graph, e);
        total_edge_weight += VECTOR(*edge_weights)[e];
        if (VECTOR(*membership)[from] == VECTOR(*membership)[to]) {
            *quality += directed_multiplier * VECTOR(*edge_weights)[e];
        }
    }
    return total_edge_weight;
}

/* Subtracts gamma * N^out_c * N^in_c for every cluster from *quality. */
static igraph_error_t leiden_quality_subtract_mass(const igraph_t *graph,
                                                   const igraph_vector_t *vertex_out_weights,
                                                   const igraph_vector_t *vertex_in_weights,
                                                   const igraph_vector_int_t *membership,
                                                   igraph_int_t nb_clusters,
                                                   igraph_real_t resolution,
                                                   igraph_real_t *quality) {
    const igraph_int_t vcount = igraph_vcount(graph);
    const igraph_bool_t directed = (vertex_in_weights != NULL);
    igraph_vector_t cluster_out_weights, cluster_in_weights;

    IGRAPH_VECTOR_INIT_FINALLY(&cluster_out_weights, vcount);
    if (directed) {
        IGRAPH_VECTOR_INIT_FINALLY(&cluster_in_weights, vcount);
    }
    for (igraph_int_t i = 0; i < vcount; i++) {
        const igraph_int_t c = VECTOR(*membership)[i];
        VECTOR(cluster_out_weights)[c] += VECTOR(*vertex_out_weights)[i];
        if (directed) {
            VECTOR(cluster_in_weights)[c] += VECTOR(*vertex_in_weights)[i];
        }
    }
    for (igraph_int_t c = 0; c < nb_clusters; c++) {
        if (directed) {
            *quality -= resolution * VECTOR(cluster_out_weights)[c] * VECTOR(cluster_in_weights)[c];
        } else {
            *quality -= resolution * VECTOR(cluster_out_weights)[c] * VECTOR(cluster_out_weights)[c];
        }
    }
    if (directed) {
        igraph_vector_destroy(&cluster_in_weights);
        IGRAPH_FINALLY_CLEAN(1);
    }
    igraph_vector_destroy(&cluster_out_weights);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* The quality of a partition with `nb_clusters` clusters numbered 0 .. nb - 1. */
static igraph_error_t leiden_quality(const igraph_t *graph,
                                     const igraph_vector_t *edge_weights,
                                     const igraph_vector_t *vertex_out_weights,
                                     const igraph_vector_t *vertex_in_weights,
                                     const igraph_vector_int_t *membership,
                                     igraph_int_t nb_clusters,
                                     igraph_real_t resolution,
                                     igraph_real_t *quality) {
    const igraph_real_t directed_multiplier = vertex_in_weights != NULL ? 1.0 : 2.0;
    igraph_real_t total_edge_weight;

    *quality = 0.0;
    total_edge_weight = leiden_quality_add_internal_weight(graph, edge_weights, membership,
                                                           directed_multiplier, quality);
    IGRAPH_CHECK(leiden_quality_subtract_mass(graph, vertex_out_weights, vertex_in_weights,
                                              membership, nb_clusters, resolution, quality));
    *quality /= (directed_multiplier * total_edge_weight);
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 3.6  Multilevel driver
 * -----------------------------------------------------------------------------
 *
 * One call runs local moving, refinement and aggregation, then the same on
 * the aggregate graph, and so on while local moving leaves some cluster with
 * more than one (aggregate) vertex. Level 0 works on the caller's graph and
 * vectors; higher levels on the aggregate storage of leiden_levels_t.
 * aggregate_vertex[i] is the aggregate vertex that contains original vertex i
 * at the current level; the original membership is refreshed from it at the
 * start of every level after the first that continues.
 */

typedef struct {
    igraph_t aggregated_graph;
    igraph_bool_t has_aggregated_graph;           /* aggregated_graph is valid */
    igraph_vector_t aggregated_edge_weights;
    igraph_vector_t aggregated_vertex_out_weights;
    igraph_vector_t aggregated_vertex_in_weights;  /* directed graphs only */
    igraph_vector_int_t aggregated_membership;
    /* Aggregation writes the next level here before it is installed. */
    igraph_vector_t tmp_edge_weights;
    igraph_vector_t tmp_vertex_out_weights;
    igraph_vector_t tmp_vertex_in_weights;         /* directed graphs only */
    igraph_vector_int_t tmp_membership;
    igraph_vector_int_list_t clusters;             /* members of each cluster */
    igraph_vector_int_t aggregate_vertex;          /* original vertex -> aggregate vertex */
    igraph_vector_int_t refined_membership;
} leiden_levels_t;

/* The graph, weights and membership of the level being optimized. */
typedef struct {
    igraph_t *graph;
    igraph_vector_t *edge_weights;
    igraph_vector_t *vertex_out_weights;
    igraph_vector_t *vertex_in_weights;            /* NULL for undirected graphs */
    igraph_vector_int_t *membership;
} leiden_level_t;

static void leiden_levels_destroy(leiden_levels_t *levels) {
    igraph_vector_int_destroy(&levels->refined_membership);
    igraph_vector_int_destroy(&levels->aggregate_vertex);
    igraph_vector_int_list_destroy(&levels->clusters);
    igraph_vector_int_destroy(&levels->tmp_membership);
    igraph_vector_destroy(&levels->tmp_vertex_in_weights);
    igraph_vector_destroy(&levels->tmp_vertex_out_weights);
    igraph_vector_destroy(&levels->tmp_edge_weights);
    igraph_vector_int_destroy(&levels->aggregated_membership);
    igraph_vector_destroy(&levels->aggregated_vertex_in_weights);
    igraph_vector_destroy(&levels->aggregated_vertex_out_weights);
    igraph_vector_destroy(&levels->aggregated_edge_weights);
    if (levels->has_aggregated_graph) {
        igraph_destroy(&levels->aggregated_graph);
    }
}

static igraph_error_t leiden_levels_init(leiden_levels_t *levels, igraph_int_t n,
                                         igraph_bool_t directed) {
    IGRAPH_CHECK(igraph_vector_init(&levels->tmp_edge_weights, 0));
    IGRAPH_CHECK(igraph_vector_init(&levels->tmp_vertex_out_weights, 0));
    if (directed) {
        IGRAPH_CHECK(igraph_vector_init(&levels->tmp_vertex_in_weights, 0));
    }
    IGRAPH_CHECK(igraph_vector_int_init(&levels->tmp_membership, 0));
    IGRAPH_CHECK(igraph_vector_int_list_init(&levels->clusters, n));
    IGRAPH_CHECK(igraph_vector_int_init_range(&levels->aggregate_vertex, 0, n));
    IGRAPH_CHECK(igraph_vector_int_init(&levels->refined_membership, 0));
    IGRAPH_CHECK(igraph_empty(&levels->aggregated_graph, 0, directed));
    levels->has_aggregated_graph = true;
    IGRAPH_CHECK(igraph_vector_init(&levels->aggregated_edge_weights, 0));
    IGRAPH_CHECK(igraph_vector_init(&levels->aggregated_vertex_out_weights, 0));
    if (directed) {
        IGRAPH_CHECK(igraph_vector_init(&levels->aggregated_vertex_in_weights, 0));
    }
    IGRAPH_CHECK(igraph_vector_int_init(&levels->aggregated_membership, 0));
    return IGRAPH_SUCCESS;
}

/* Writes the current level's clustering back to the original vertices. */
static void leiden_levels_project(const leiden_levels_t *levels,
                                  const leiden_level_t *level,
                                  igraph_vector_int_t *membership) {
    const igraph_int_t n = igraph_vector_int_size(&levels->aggregate_vertex);

    for (igraph_int_t i = 0; i < n; i++) {
        const igraph_int_t v_aggregate = VECTOR(levels->aggregate_vertex)[i];
        VECTOR(*membership)[i] = VECTOR(*level->membership)[v_aggregate];
    }
}

/* Refines every cluster of the level (phase 2) into
 * levels->refined_membership. If refinement merged nothing, the unrefined
 * clusters are used instead. Returns the number of refined clusters. */
static igraph_error_t leiden_levels_refine(leiden_levels_t *levels,
                                           const leiden_level_t *level,
                                           const igraph_inclist_t *edges_per_vertex,
                                           const leiden_options_t *options,
                                           igraph_int_t nb_clusters,
                                           igraph_int_t *nb_refined_clusters) {
    const igraph_int_t level_size = igraph_vcount(level->graph);

    IGRAPH_CHECK(leiden_get_clusters(level->membership, &levels->clusters));
    IGRAPH_CHECK(igraph_vector_int_resize(&levels->refined_membership, level_size));

    *nb_refined_clusters = 0;
    for (igraph_int_t c = 0; c < nb_clusters; c++) {
        igraph_vector_int_t *cluster = igraph_vector_int_list_get_ptr(&levels->clusters, c);
        IGRAPH_CHECK(leiden_merge_vertices(level->graph, edges_per_vertex, level->edge_weights,
                                           level->vertex_out_weights, level->vertex_in_weights,
                                           cluster, level->membership, c, options,
                                           nb_refined_clusters, &levels->refined_membership));
        igraph_vector_int_clear(cluster);
    }

    if (*nb_refined_clusters >= level_size) {
        IGRAPH_CHECK(igraph_vector_int_update(&levels->refined_membership, level->membership));
        *nb_refined_clusters = nb_clusters;
    }
    return IGRAPH_SUCCESS;
}

/* Moves every original vertex to the aggregate vertex of its refined
 * cluster. */
static void leiden_levels_descend(leiden_levels_t *levels) {
    const igraph_int_t n = igraph_vector_int_size(&levels->aggregate_vertex);

    for (igraph_int_t i = 0; i < n; i++) {
        const igraph_int_t v_aggregate = VECTOR(levels->aggregate_vertex)[i];
        VECTOR(levels->aggregate_vertex)[i] = VECTOR(levels->refined_membership)[v_aggregate];
    }
}

/* Makes the freshly aggregated graph the current level. At level 0 the
 * level view switches from the caller's storage to the aggregate storage. */
static igraph_error_t leiden_levels_install(leiden_levels_t *levels, leiden_level_t *level,
                                            igraph_int_t level_number) {
    if (level_number == 0) {
        level->graph = &levels->aggregated_graph;
        level->edge_weights = &levels->aggregated_edge_weights;
        level->vertex_out_weights = &levels->aggregated_vertex_out_weights;
        if (level->vertex_in_weights) {
            level->vertex_in_weights = &levels->aggregated_vertex_in_weights;
        }
        level->membership = &levels->aggregated_membership;
    }
    IGRAPH_CHECK(igraph_vector_update(level->edge_weights, &levels->tmp_edge_weights));
    IGRAPH_CHECK(igraph_vector_update(level->vertex_out_weights, &levels->tmp_vertex_out_weights));
    if (level->vertex_in_weights) {
        IGRAPH_CHECK(igraph_vector_update(level->vertex_in_weights, &levels->tmp_vertex_in_weights));
    }
    IGRAPH_CHECK(igraph_vector_int_update(level->membership, &levels->tmp_membership));
    return IGRAPH_SUCCESS;
}

/* Refines and aggregates the current level and descends to the aggregate
 * graph (phases 2 and 3). */
static igraph_error_t leiden_levels_coarsen(leiden_levels_t *levels, leiden_level_t *level,
                                            const igraph_inclist_t *edges_per_vertex,
                                            const leiden_options_t *options,
                                            igraph_int_t nb_clusters,
                                            igraph_int_t level_number) {
    igraph_int_t nb_refined_clusters;

    IGRAPH_CHECK(leiden_levels_refine(levels, level, edges_per_vertex, options, nb_clusters,
                                      &nb_refined_clusters));
    leiden_levels_descend(levels);
    IGRAPH_CHECK(leiden_aggregate(level->graph, edges_per_vertex, level->edge_weights,
                                  level->vertex_out_weights, level->vertex_in_weights,
                                  level->membership, &levels->refined_membership,
                                  nb_refined_clusters, &levels->aggregated_graph,
                                  &levels->tmp_edge_weights, &levels->tmp_vertex_out_weights,
                                  level->vertex_in_weights ? &levels->tmp_vertex_in_weights : NULL,
                                  &levels->tmp_membership));
    return leiden_levels_install(levels, level, level_number);
}

/* Optimizes one level: local moving, then (unless local_move_only, or every
 * cluster is a single vertex) refinement, aggregation and descent. Sets
 * *continue_clustering if a coarser level follows, and *level_changed if
 * local moving moved any vertex of this level. */
static igraph_error_t leiden_levels_step(leiden_levels_t *levels, leiden_level_t *level,
                                         const leiden_options_t *options,
                                         igraph_int_t level_number,
                                         igraph_vector_int_t *membership,
                                         igraph_int_t *nb_clusters,
                                         igraph_bool_t *level_changed,
                                         igraph_bool_t *continue_clustering) {
    igraph_inclist_t edges_per_vertex;

    IGRAPH_CHECK(igraph_inclist_init(level->graph, &edges_per_vertex, IGRAPH_ALL,
                                     IGRAPH_LOOPS_TWICE));
    IGRAPH_FINALLY(igraph_inclist_destroy, &edges_per_vertex);

    *level_changed = false;
    IGRAPH_CHECK(leiden_fastmove_vertices(level->graph, &edges_per_vertex, level->edge_weights,
                                          level->vertex_out_weights, level->vertex_in_weights,
                                          options, nb_clusters, level->membership, level_changed));

    *continue_clustering = options->local_move_only ?
                           false : (*nb_clusters < igraph_vcount(level->graph));
    if (*continue_clustering) {
        if (level_number > 0) {
            leiden_levels_project(levels, level, membership);
        }
        IGRAPH_CHECK(leiden_levels_coarsen(levels, level, &edges_per_vertex, options,
                                           *nb_clusters, level_number));
    }

    igraph_inclist_destroy(&edges_per_vertex);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* One Leiden iteration on (graph, weights), starting from and updating
 * `membership`. Renumbers the membership, reports the number of clusters,
 * sets *changed if anything moved, and computes the quality if requested. */
static igraph_error_t community_leiden(const igraph_t *graph,
                                       igraph_vector_t *edge_weights,
                                       igraph_vector_t *vertex_out_weights,
                                       igraph_vector_t *vertex_in_weights,
                                       const leiden_options_t *options,
                                       igraph_vector_int_t *membership,
                                       igraph_int_t *nb_clusters,
                                       igraph_real_t *quality,
                                       igraph_bool_t *changed) {
    const igraph_bool_t directed = (vertex_in_weights != NULL);
    leiden_levels_t levels = { .has_aggregated_graph = false };
    leiden_level_t level = {
        .graph = (igraph_t *) graph,
        .edge_weights = edge_weights,
        .vertex_out_weights = vertex_out_weights,
        .vertex_in_weights = vertex_in_weights,
        .membership = membership
    };
    igraph_bool_t continue_clustering, level_changed;
    igraph_int_t level_number = 0;

    IGRAPH_FINALLY(leiden_levels_destroy, &levels);
    IGRAPH_CHECK(leiden_levels_init(&levels, igraph_vcount(graph), directed));

    /* Cluster indices must satisfy 0 <= c < n. */
    IGRAPH_CHECK(igraph_reindex_membership(membership, NULL, nb_clusters));

    *changed = false;
    do {
        IGRAPH_CHECK(leiden_levels_step(&levels, &level, options, level_number, membership,
                                        nb_clusters, &level_changed, &continue_clustering));
        if (level_changed) {
            *changed = true;
        }
        if (continue_clustering) {
            level_number++;
        }
    } while (continue_clustering);

    /* A level that continues writes its clustering back to the original
     * vertices, but the last level does not. If its local moving moved
     * aggregate vertices (it can split clusters, e.g. with negative edge
     * weights), the result would otherwise keep the previous level's
     * clustering while reporting a change -- and with n_iterations < 0 the
     * next iteration would repeat the same moves forever. */
    if (level_number > 0 && level_changed) {
        leiden_levels_project(&levels, &level, membership);
    }

    leiden_levels_destroy(&levels);
    IGRAPH_FINALLY_CLEAN(1);

    if (quality) {
        IGRAPH_CHECK(leiden_quality(graph, edge_weights, vertex_out_weights, vertex_in_weights,
                                    membership, *nb_clusters, options->resolution, quality));
    }
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 3.7  Disjoint entry: start state, iterations and certificate
 * -----------------------------------------------------------------------------
 *
 * Implements the max_memberships == 1 branch of
 * igraph_community_leiden_with_constraints(): validates the start state and
 * weights, iterates the multilevel driver, and, when asked to converge,
 * finishes with local-moving sweeps until no vertex moves (a Nash
 * certificate: Definition 3 / Proposition 1 of Felipe, Avrachenkov &
 * Menasche, Physica A 680:130989, 2025).
 */

typedef struct {
    igraph_vector_int_t owned_membership;   /* used when the caller gave only a list */
    leiden_weights_t edge_weights;
    leiden_weights_t vertex_out_weights;
} leiden_disjoint_t;

static void leiden_disjoint_destroy(leiden_disjoint_t *run) {
    leiden_weights_destroy(&run->vertex_out_weights);
    leiden_weights_destroy(&run->edge_weights);
    igraph_vector_int_destroy(&run->owned_membership);
}

/* Chooses the membership vector to optimize and fills it with the start
 * partition: the caller's vector, or an owned vector seeded from the first
 * label of each row of `memberships` (or from singletons). */
static igraph_error_t leiden_disjoint_start(leiden_disjoint_t *run, igraph_int_t vcount,
                                            igraph_bool_t start,
                                            igraph_vector_int_t *membership,
                                            const igraph_vector_int_list_t *memberships,
                                            igraph_vector_int_t **mem) {
    if (membership) {
        *mem = membership;
        if (!start) {
            IGRAPH_CHECK(igraph_vector_int_range(membership, 0, vcount));
        } else if (igraph_vector_int_size(membership) != vcount) {
            IGRAPH_ERROR("Membership vector length does not equal the number of vertices.",
                         IGRAPH_EINVAL);
        }
        return IGRAPH_SUCCESS;
    }
    if (!memberships) {
        IGRAPH_ERROR("Either membership or memberships must be provided.", IGRAPH_EINVAL);
    }
    IGRAPH_CHECK(igraph_vector_int_init(&run->owned_membership, vcount));
    *mem = &run->owned_membership;
    if (start && igraph_vector_int_list_size(memberships) == vcount) {
        for (igraph_int_t v = 0; v < vcount; v++) {
            const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
            VECTOR(**mem)[v] = igraph_vector_int_size(sigma) > 0 ? VECTOR(*sigma)[0] : v;
        }
    } else {
        IGRAPH_CHECK(igraph_vector_int_range(*mem, 0, vcount));
    }
    return IGRAPH_SUCCESS;
}

/* With a count limit: builds the deterministic feasible start v mod K when
 * no start was given, and rejects a start that violates the limit. */
static igraph_error_t leiden_disjoint_check_counts(igraph_vector_int_t *mem, igraph_int_t vcount,
                                                   igraph_bool_t start,
                                                   igraph_int_t max_total_communities,
                                                   igraph_int_t n_communities) {
    igraph_int_t initial_clusters;

    if (max_total_communities <= 0 && n_communities <= 0) {
        return IGRAPH_SUCCESS;
    }
    if (n_communities > vcount) {
        IGRAPH_ERROR("n_communities must not exceed the number of vertices for a partition.",
                     IGRAPH_EINVAL);
    }
    if (!start) {
        const igraph_int_t target = n_communities > 0 ? n_communities :
                                    max_total_communities < vcount ? max_total_communities : vcount;
        for (igraph_int_t v = 0; v < vcount; v++) {
            VECTOR(*mem)[v] = v % target;
        }
    }
    if (vcount > 0 && igraph_vector_int_min(mem) < 0) {
        IGRAPH_ERROR("Initial membership labels must be non-negative.", IGRAPH_EINVAL);
    }
    IGRAPH_CHECK(igraph_reindex_membership(mem, NULL, &initial_clusters));
    if (max_total_communities > 0 && initial_clusters > max_total_communities) {
        IGRAPH_ERROR("Initial membership exceeds max_total_communities.", IGRAPH_EINVAL);
    }
    if (n_communities > 0 && initial_clusters != n_communities) {
        IGRAPH_ERROR("Initial membership does not contain exactly n_communities communities.",
                     IGRAPH_EINVAL);
    }
    return IGRAPH_SUCCESS;
}

/* Validates the weight vectors and resolves NULL ones to unit weights. For
 * directed graphs, missing in-weights equal the out-weights. */
static igraph_error_t leiden_disjoint_weights(leiden_disjoint_t *run, const igraph_t *graph,
                                              const igraph_vector_t *edge_weights,
                                              const igraph_vector_t *vertex_out_weights,
                                              const igraph_vector_t *vertex_in_weights,
                                              igraph_vector_t **in_weights) {
    const igraph_int_t vcount = igraph_vcount(graph);
    const igraph_int_t ecount = igraph_ecount(graph);
    const igraph_bool_t directed = igraph_is_directed(graph);

    if (edge_weights && igraph_vector_size(edge_weights) != ecount) {
        IGRAPH_ERRORF("Edge weight vector length (%" IGRAPH_PRId ") does not match number of edges (%" IGRAPH_PRId ").",
                      IGRAPH_EINVAL, igraph_vector_size(edge_weights), ecount);
    }
    IGRAPH_CHECK(leiden_weights_init(&run->edge_weights, edge_weights, ecount));

    if (vertex_out_weights && igraph_vector_size(vertex_out_weights) != vcount) {
        IGRAPH_ERRORF("Vertex %sweight vector length (%" IGRAPH_PRId ") does not match number of vertices (%" IGRAPH_PRId ").",
                      IGRAPH_EINVAL, directed ? "out-" : "",
                      igraph_vector_size(vertex_out_weights), vcount);
    }
    IGRAPH_CHECK(leiden_weights_init(&run->vertex_out_weights, vertex_out_weights, vcount));

    if (!directed) {
        if (vertex_in_weights) {
            IGRAPH_ERROR("Vertex in-weights must not be given for undirected graphs.", IGRAPH_EINVAL);
        }
        *in_weights = NULL;
    } else if (vertex_in_weights) {
        if (igraph_vector_size(vertex_in_weights) != vcount) {
            IGRAPH_ERRORF("Vertex in-weight vector length (%" IGRAPH_PRId ") does not match number of vertices (%" IGRAPH_PRId ").",
                          IGRAPH_EINVAL, igraph_vector_size(vertex_in_weights), vcount);
        }
        *in_weights = (igraph_vector_t *) vertex_in_weights;
    } else {
        *in_weights = run->vertex_out_weights.vector;
    }
    return IGRAPH_SUCCESS;
}

/* Runs the requested number of Leiden iterations (until nothing changes if
 * n_iterations < 0), then the certificate sweeps. Local-moving-only runs
 * need no extra sweep: their last iteration already moved nothing. */
static igraph_error_t leiden_disjoint_iterate(const igraph_t *graph,
                                              igraph_vector_t *edge_weights,
                                              igraph_vector_t *vertex_out_weights,
                                              igraph_vector_t *vertex_in_weights,
                                              const leiden_options_t *options,
                                              igraph_int_t n_iterations,
                                              igraph_vector_int_t *mem,
                                              igraph_int_t *nb_clusters,
                                              igraph_real_t *quality) {
    leiden_options_t sweep = *options;
    igraph_bool_t changed = true;

    for (igraph_int_t itr = 0; n_iterations < 0 ? changed : itr < n_iterations; itr++) {
        IGRAPH_CHECK(community_leiden(graph, edge_weights, vertex_out_weights, vertex_in_weights,
                                      options, mem, nb_clusters, quality, &changed));
    }

    /* Refinement and aggregation may rewrite a locally stable partition. */
    if (n_iterations < 0 && !options->local_move_only) {
        sweep.local_move_only = true;
        do {
            changed = false;
            IGRAPH_CHECK(community_leiden(graph, edge_weights, vertex_out_weights,
                                          vertex_in_weights, &sweep, mem, nb_clusters, quality,
                                          &changed));
        } while (changed);
    }
    return IGRAPH_SUCCESS;
}

/* Copies a partition into the list form, one label per vertex. */
static igraph_error_t leiden_disjoint_to_list(const igraph_vector_int_t *mem,
                                              igraph_vector_int_list_t *memberships) {
    const igraph_int_t vcount = igraph_vector_int_size(mem);

    IGRAPH_CHECK(igraph_vector_int_list_resize(memberships, vcount));
    for (igraph_int_t v = 0; v < vcount; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        IGRAPH_CHECK(igraph_vector_int_resize(sigma, 1));
        VECTOR(*sigma)[0] = VECTOR(*mem)[v];
    }
    return IGRAPH_SUCCESS;
}

/* The disjoint (max_memberships == 1) path of
 * igraph_community_leiden_with_constraints(). */
static igraph_error_t leiden_disjoint_run(const igraph_t *graph,
                                          const igraph_vector_t *edge_weights,
                                          const igraph_vector_t *vertex_out_weights,
                                          const igraph_vector_t *vertex_in_weights,
                                          const leiden_options_t *options,
                                          igraph_bool_t start,
                                          igraph_int_t n_iterations,
                                          igraph_vector_int_t *membership,
                                          igraph_vector_int_list_t *memberships,
                                          igraph_int_t *nb_clusters,
                                          igraph_real_t *quality) {
    const igraph_int_t vcount = igraph_vcount(graph);
    leiden_disjoint_t run = { .edge_weights = { .vector = NULL } };
    igraph_vector_int_t *mem;
    igraph_vector_t *in_weights;
    igraph_int_t i_nb_clusters;

    if (!nb_clusters) {
        nb_clusters = &i_nb_clusters;
    }

    IGRAPH_FINALLY(leiden_disjoint_destroy, &run);
    IGRAPH_CHECK(leiden_disjoint_start(&run, vcount, start, membership, memberships, &mem));
    IGRAPH_CHECK(leiden_disjoint_check_counts(mem, vcount, start,
                                              options->max_total_communities,
                                              options->n_communities));
    IGRAPH_CHECK(leiden_disjoint_weights(&run, graph, edge_weights, vertex_out_weights,
                                         vertex_in_weights, &in_weights));

    IGRAPH_CHECK(leiden_disjoint_iterate(graph, run.edge_weights.vector,
                                         run.vertex_out_weights.vector, in_weights, options,
                                         n_iterations, mem, nb_clusters, quality));

    /* A zero budget performs no iteration; report the (renumbered) start. */
    if (n_iterations == 0) {
        IGRAPH_CHECK(igraph_reindex_membership(mem, NULL, nb_clusters));
        if (quality) {
            IGRAPH_CHECK(leiden_quality(graph, run.edge_weights.vector,
                                        run.vertex_out_weights.vector, in_weights, mem,
                                        *nb_clusters, options->resolution, quality));
        }
    }

    if (memberships) {
        IGRAPH_CHECK(leiden_disjoint_to_list(mem, memberships));
    }

    leiden_disjoint_destroy(&run);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}


/* =============================================================================
 * Section 4  Overlapping Leiden (unit-l2 CPM hedonic game)
 * =============================================================================
 */

/* -----------------------------------------------------------------------------
 * Section 4.1  Model, notation and diagnostic records
 * -----------------------------------------------------------------------------
 *
 * This section extends Leiden from partitions to covers, following the
 * exact-potential-game formulation of the CPM in Felipe, Avrachenkov &
 * Menasche, Physica A 680:130989 (2025), "From Leiden to Pleasure Island",
 * DOI 10.1016/j.physa.2025.130989. Each vertex v holds a sorted,
 * duplicate-free set sigma_v of at most M labels.
 *
 * --- The potential ---
 *
 * Vertex v participates in each of its labels with intensity
 * f_v = 1 / sqrt(k_v), k_v = |sigma_v|. The unnormalized potential is
 *
 *   Q(sigma) = sum_c [ E_c - (gamma/2) S_c^2 ],
 *     E_c = sum_{i<j} A_ij f_i f_j [c in sigma_i and sigma_j],
 *     S_c = sum_i n_i f_i [c in sigma_i].
 *
 * The pairwise coefficient kappa_ij = |sigma_i & sigma_j| / sqrt(k_i k_j)
 * is at most 1 (Cauchy-Schwarz; equality iff sigma_i == sigma_j), so no pair
 * of vertices can amplify an edge beyond its weight, and on a partition
 * (all k = 1) Q is exactly the CPM quality of Section 3.5. The reported
 * quality divides Q by the total edge weight.
 *
 * Why 1/sqrt(k) and not 1/k? With 1/k the diagonal term (n_v f_v)^2 depends
 * on k, and an isolated vertex with gamma > 0 would prefer two private labels
 * (-gamma/4) to one (-gamma/2). With 1/sqrt(k) the diagonal term is the
 * constant n_v^2, the potential is exact, it reduces to the CPM, and a second
 * label pays exactly when its value exceeds (sqrt(2) - 1) times the first.
 *
 * --- Best responses ---
 *
 * With
 *
 *   g_c(v) = L_v^c - gamma n_v W_v^c,
 *     L_v^c = sum_{u ~ v} A_uv f_u [c in sigma_u]   (support of c at v),
 *     W_v^c = S_c - n_v f_v [c in sigma_v]          (mass of c without v),
 *
 * the contribution of v with label set sigma is, up to a constant,
 *
 *   U_v(sigma) = ( sum_{c in sigma} g_c(v) ) / sqrt(|sigma|),
 *
 * and Delta U_v = Delta Q for every unilateral change of sigma_v: Q is an
 * exact potential. Since g_c(v) does not depend on sigma_v, the best set is
 * a prefix of the labels sorted by gain: choose j <= M maximizing
 * (sum of the j largest gains) / sqrt(j) (Section 4.4.5). Adding, removing
 * and substituting labels are just ways of reading the change of prefix.
 *
 * Candidates (Section 4.4.3): v's labels, its neighbours' labels, one empty
 * label when isolation is allowed (gain 0, which subsumes leaving to a new
 * community), and "omitted" labels -- occupied labels held by no neighbour --
 * when they can beat the empty label: the least massive one for
 * gamma * n_v > 0 with isolation disabled, and the most massive ones for
 * gamma * n_v < 0. The label index of Section 2 finds them without a scan.
 *
 * Adding a label rescales all of v's intensities, so entry pays only if
 * g_c > (sqrt((k+1)/k) - 1) * sum of the current gains. This explains one
 * entry decision, not a general sparsity bound: equal positive gains can make
 * every entry attractive, and duplicate-label equilibria exist. M is the only
 * incidence bound enforced here.
 *
 * --- Convergence ---
 *
 * In exact arithmetic strict improvements terminate on the finite set of
 * covers. In floating point, improvements within the tie margin of Section
 * 1.1 are ties, and a progress ceiling turns unexpected churn into an
 * internal error. For a fixed profile each deviation gain is affine in
 * gamma, so best-response checks at two resolutions certify the interval
 * between them.
 *
 * --- Multilevel phases on the token graph (Sections 4.5 and 4.6) ---
 *
 * After local moving, every (vertex, label) pair becomes a token of weight
 * n_v f_v, and every edge (u, v) becomes token edges of weight A_uv f_u f_v.
 * With the k's frozen, a collision-free token partition has exactly the
 * unnormalized potential of the cover it projects to, so the disjoint
 * refinement and aggregation of Section 3 run unchanged on tokens (in
 * tolerant mode). Merges on coarse levels can put two tokens of one vertex
 * into the same label; projection collapses such duplicates. Every proposal
 * is then checked in the original graph (Section 4.7) and kept only if it
 * improves on the cover reached by local moving.
 */

/* Where the diagnostic entry point writes its records (NULL matrices when
 * not requested). */
typedef struct {
    igraph_matrix_t *move_trace;
    igraph_matrix_t *projection_trace;
    igraph_int_t stage;             /* outer iteration; negative for certificate sweeps */
    igraph_int_t move_sequence;
    igraph_real_t original_weight;  /* total edge weight of the original graph */
} overlap_trace_t;

/* Measurements of one multilevel iteration, for the projection trace. */
typedef struct {
    igraph_real_t original_weight;
    igraph_real_t token_weight;
    igraph_real_t quality_after_local;
    igraph_real_t original_unnormalized;
    igraph_real_t token_initial_quality;
    igraph_real_t token_initial_unnormalized;
    igraph_real_t token_identity_abs_error;
    igraph_real_t token_final_quality;
    igraph_real_t quality_projected;
    igraph_int_t token_count;
    igraph_int_t token_edge_count;
    igraph_int_t collision_count;
    igraph_bool_t local_changed;
    igraph_bool_t token_changed;
    igraph_int_t labels_local;
    igraph_int_t labels_proposed;
    igraph_bool_t dedup_changed;
} overlap_checkpoint_t;

/* Appends one row of `width` values to a trace matrix. */
static igraph_error_t overlap_trace_append(igraph_matrix_t *trace, const igraph_real_t *values,
                                           igraph_int_t width) {
    const igraph_int_t row = igraph_matrix_nrow(trace);

    if (igraph_matrix_ncol(trace) != width) {
        IGRAPH_ERROR("Overlapping Leiden diagnostic trace width mismatch.", IGRAPH_EINVAL);
    }
    IGRAPH_CHECK(igraph_matrix_add_rows(trace, 1));
    for (igraph_int_t column = 0; column < width; column++) {
        MATRIX(*trace, row, column) = values[column];
    }
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 4.2  Cover utilities
 * -----------------------------------------------------------------------------
 *
 * A cover is an igraph_vector_int_list_t with one sorted, duplicate-free,
 * non-empty row of labels per vertex.
 */

/* The largest label in the cover, or -1 if it has none. */
static igraph_int_t overlap_max_label(const igraph_vector_int_list_t *memberships) {
    const igraph_int_t n = igraph_vector_int_list_size(memberships);
    igraph_int_t maxid = -1;

    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);
        for (igraph_int_t idx = 0; idx < k; idx++) {
            if (VECTOR(*sigma)[idx] > maxid) {
                maxid = VECTOR(*sigma)[idx];
            }
        }
    }
    return maxid;
}

/* The number of distinct labels, without renumbering them. */
static igraph_error_t overlap_count_labels(const igraph_vector_int_list_t *memberships,
                                           igraph_int_t *count) {
    const igraph_int_t n = igraph_vector_int_list_size(memberships);
    igraph_int_t id_count, distinct = 0;
    igraph_vector_bool_t seen;

    IGRAPH_SAFE_ADD(overlap_max_label(memberships), 1, &id_count);
    IGRAPH_VECTOR_BOOL_INIT_FINALLY(&seen, id_count);
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);
        for (igraph_int_t idx = 0; idx < k; idx++) {
            const igraph_int_t c = VECTOR(*sigma)[idx];
            if (!VECTOR(seen)[c]) {
                VECTOR(seen)[c] = true;
                distinct++;
            }
        }
    }
    *count = distinct;

    igraph_vector_bool_destroy(&seen);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* Renumbers the labels 0, 1, ... in order of first appearance, keeps every
 * row sorted, and returns the number of labels. */
static igraph_error_t overlap_compact(igraph_vector_int_list_t *memberships,
                                      igraph_int_t *nb_clusters) {
    const igraph_int_t n = igraph_vector_int_list_size(memberships);
    igraph_int_t id_count, next = 0;
    igraph_vector_int_t new_id;

    IGRAPH_SAFE_ADD(overlap_max_label(memberships), 1, &id_count);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&new_id, id_count);
    igraph_vector_int_fill(&new_id, -1);
    for (igraph_int_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);
        for (igraph_int_t idx = 0; idx < k; idx++) {
            const igraph_int_t c = VECTOR(*sigma)[idx];
            if (VECTOR(new_id)[c] < 0) {
                VECTOR(new_id)[c] = next;
                next++;
            }
            VECTOR(*sigma)[idx] = VECTOR(new_id)[c];
        }
        igraph_vector_int_sort(sigma);
    }
    *nb_clusters = next;

    igraph_vector_int_destroy(&new_id);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* Copies every row of `source` into the equally long `target`. */
static igraph_error_t overlap_copy_cover(igraph_vector_int_list_t *target,
                                         const igraph_vector_int_list_t *source) {
    const igraph_int_t n = igraph_vector_int_list_size(source);

    for (igraph_int_t v = 0; v < n; v++) {
        IGRAPH_CHECK(igraph_vector_int_update(igraph_vector_int_list_get_ptr(target, v),
                                              igraph_vector_int_list_get_ptr(source, v)));
    }
    return IGRAPH_SUCCESS;
}

/* An FNV-1a fingerprint of the cover, reported by progress-ceiling errors. */
static igraph_uint_t overlap_cover_hash(const igraph_vector_int_list_t *memberships) {
    igraph_uint_t hash = (igraph_uint_t) 1469598103934665603ULL;
    const igraph_int_t n = igraph_vector_int_list_size(memberships);

    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);

        hash ^= (igraph_uint_t) (v + 1);
        hash *= (igraph_uint_t) 1099511628211ULL;
        hash ^= (igraph_uint_t) k;
        hash *= (igraph_uint_t) 1099511628211ULL;
        for (igraph_int_t idx = 0; idx < k; idx++) {
            hash ^= (igraph_uint_t) (VECTOR(*sigma)[idx] + 1);
            hash *= (igraph_uint_t) 1099511628211ULL;
        }
    }
    return hash;
}

/* -----------------------------------------------------------------------------
 * Section 4.3  Potential (quality) of a cover
 * -----------------------------------------------------------------------------
 *
 *   quality = (1 / 2W) sum_c ( 2 E_c - gamma S_c^2 ),   W = total edge weight,
 *
 * computed directly from the rows; on partitions it equals the disjoint
 * quality of Section 3.5. The public entry points reject self-loops; the loop branch
 * below is defensive. The extended variant also reports the summed term
 * magnitude and the number of terms, which bound the rounding error of the
 * recursive summation (|error| <= count * epsilon * magnitude; Higham,
 * Thm. 4.1), used by the diagnostic comparisons.
 */

/* |a & b| for two sorted label rows. */
static igraph_int_t overlap_shared_labels(const igraph_vector_int_t *a,
                                          const igraph_vector_int_t *b) {
    const igraph_int_t ka = igraph_vector_int_size(a), kb = igraph_vector_int_size(b);
    igraph_int_t ia = 0, ib = 0, shared = 0;

    while (ia < ka && ib < kb) {
        if (VECTOR(*a)[ia] < VECTOR(*b)[ib]) {
            ia++;
        } else if (VECTOR(*a)[ia] > VECTOR(*b)[ib]) {
            ib++;
        } else {
            shared++;
            ia++;
            ib++;
        }
    }
    return shared;
}

/* The quality of a cover, plus (optionally) the magnitude and number of the
 * summed terms.
 *
 * The three floating-point loops below -- label masses, edge support and
 * crowding -- deliberately stay in this one function with local
 * accumulators, exactly as released. The compiler decides per loop whether
 * to fuse multiply-adds and how to vectorize (the released arm64 build fuses
 * the crowding term only outside its four-way unrolled body), so moving a
 * loop into a helper changes the last bits of the quality. Those bits matter:
 * the multilevel guard of Section 4.7 compares two such qualities. */
static igraph_error_t overlap_quality_ext(const igraph_t *graph,
                                          const igraph_vector_t *edge_weights,
                                          const igraph_vector_t *node_weights,
                                          const igraph_vector_int_list_t *memberships,
                                          igraph_real_t resolution,
                                          igraph_real_t *quality,
                                          igraph_real_t *term_magnitude,
                                          igraph_int_t *term_count) {
    const igraph_int_t n = igraph_vcount(graph);
    const igraph_int_t m = igraph_ecount(graph);
    const igraph_int_t maxid = overlap_max_label(memberships);
    igraph_real_t total_edge_weight = 0.0, q = 0.0, magnitude = 0.0;
    igraph_vector_t comm_mass;
    igraph_int_t id_count;

    /* S_c = sum_v n_v f_v [c in sigma_v]. */
    IGRAPH_SAFE_ADD(maxid, 1, &id_count);
    IGRAPH_VECTOR_INIT_FINALLY(&comm_mass, id_count);
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);
        const igraph_real_t fv = 1.0 / sqrt((igraph_real_t) k);
        for (igraph_int_t idx = 0; idx < k; idx++) {
            VECTOR(comm_mass)[VECTOR(*sigma)[idx]] += VECTOR(*node_weights)[v] * fv;
        }
    }

    /* 2 E_c summed over labels, edge by edge: 2 w |sigma_u & sigma_v| f_u f_v. */
    for (igraph_int_t e = 0; e < m; e++) {
        const igraph_int_t from = IGRAPH_FROM(graph, e), to = IGRAPH_TO(graph, e);
        const igraph_real_t w = VECTOR(*edge_weights)[e];
        const igraph_vector_int_t *sig_f, *sig_t;
        igraph_int_t kf, kt, shared;

        total_edge_weight += w;
        if (from == to) {
            q += 2 * w;
            magnitude += fabs(2 * w);
            continue;
        }
        sig_f = igraph_vector_int_list_get_ptr(memberships, from);
        sig_t = igraph_vector_int_list_get_ptr(memberships, to);
        kf = igraph_vector_int_size(sig_f);
        kt = igraph_vector_int_size(sig_t);
        shared = overlap_shared_labels(sig_f, sig_t);
        if (shared > 0) {
            const igraph_real_t term = 2 * w * shared /
                 (sqrt((igraph_real_t) kf) * sqrt((igraph_real_t) kt));
            q += term;
            magnitude += fabs(term);
        }
    }

    /* Crowding: - gamma S_c^2. */
    for (igraph_int_t c = 0; c <= maxid; c++) {
        q -= resolution * VECTOR(comm_mass)[c] * VECTOR(comm_mass)[c];
        magnitude += fabs(resolution * VECTOR(comm_mass)[c] * VECTOR(comm_mass)[c]);
    }
    if (term_magnitude) {
        *term_magnitude = magnitude;
    }
    if (term_count) {
        *term_count = m + maxid + 1;
    }

    igraph_vector_destroy(&comm_mass);
    IGRAPH_FINALLY_CLEAN(1);

    if (!(total_edge_weight > 0.0) || !isfinite(total_edge_weight)) {
        IGRAPH_ERROR("Overlapping Leiden quality requires positive finite total edge weight.",
                     IGRAPH_EINVAL);
    }
    q /= 2.0 * total_edge_weight;
    if (!isfinite(q)) {
        IGRAPH_ERROR("Overlapping Leiden quality overflowed.", IGRAPH_EOVERFLOW);
    }
    *quality = q;
    return IGRAPH_SUCCESS;
}

/* The quality of a cover. */
static igraph_error_t overlap_quality(const igraph_t *graph,
                                      const igraph_vector_t *edge_weights,
                                      const igraph_vector_t *node_weights,
                                      const igraph_vector_int_list_t *memberships,
                                      igraph_real_t resolution,
                                      igraph_real_t *quality) {
    return overlap_quality_ext(graph, edge_weights, node_weights, memberships, resolution,
                               quality, NULL, NULL);
}

/* -----------------------------------------------------------------------------
 * Section 4.4  Local moving
 * -----------------------------------------------------------------------------
 *
 * Queue-driven like Section 3.2, but a visit computes the vertex's exact
 * best-response *set*: collect candidate labels (4.4.3), score them (4.4.4),
 * take the best sorted prefix (4.4.5), and adopt it if it improves the
 * current score beyond the tie margin (4.4.6). Rows stay sorted,
 * duplicate-free and non-empty.
 *
 * Label bookkeeping (masses S_c and member counts) is incremental; every
 * max(1024, n) queue pops it is rebuilt from the rows, the authoritative
 * state (debug builds also report any drift). A rebuild that corrects the
 * state materially re-queues every vertex. Masses are rebuilt exactly at the
 * start of every call, so a sweep without moves -- the certificate --
 * always evaluates exact masses.
 */

/* ---- Section 4.4.1  Candidate buffer -------------------------------------- */

typedef struct {
    igraph_real_t gain;   /* g_c = L_v^c - gamma * n_v * W_v^c */
    igraph_int_t comm;
} overlap_cand_t;

/* Descending gain, ties broken by ascending label, so the response is
 * deterministic. */
static int overlap_cand_cmp(const void *a, const void *b) {
    const overlap_cand_t *ca = (const overlap_cand_t *) a;
    const overlap_cand_t *cb = (const overlap_cand_t *) b;
    if (ca->gain > cb->gain) {
        return -1;
    }
    if (ca->gain < cb->gain) {
        return 1;
    }
    if (ca->comm < cb->comm) {
        return -1;
    }
    if (ca->comm > cb->comm) {
        return 1;
    }
    return 0;
}

static void overlap_cand_swap(overlap_cand_t *cand, igraph_int_t i, igraph_int_t j) {
    const overlap_cand_t tmp = cand[i];
    cand[i] = cand[j];
    cand[j] = tmp;
}

/* A growable candidate array. It starts at the neighbourhood bound and
 * grows only when a visit needs more room (earlier releases reserved
 * n * max_memberships + 1 entries per call). */
typedef struct {
    overlap_cand_t *data;
    igraph_int_t capacity;
} overlap_cand_buffer_t;

static void overlap_cand_buffer_destroy(overlap_cand_buffer_t *buffer) {
    IGRAPH_FREE(buffer->data);
    buffer->capacity = 0;
}

static igraph_error_t overlap_cand_buffer_reserve(overlap_cand_buffer_t *buffer,
                                                  igraph_int_t needed) {
    igraph_int_t newcap;
    overlap_cand_t *resized;

    if (needed <= buffer->capacity) {
        return IGRAPH_SUCCESS;
    }
    newcap = buffer->capacity > IGRAPH_INTEGER_MAX / 2 ? IGRAPH_INTEGER_MAX : 2 * buffer->capacity;
    if (newcap < needed) {
        newcap = needed;
    }
    resized = IGRAPH_REALLOC(buffer->data, newcap, overlap_cand_t);
    IGRAPH_CHECK_OOM(resized, "Insufficient memory for overlapping Leiden candidates.");
    buffer->data = resized;
    buffer->capacity = newcap;
    return IGRAPH_SUCCESS;
}

/* Appends label `comm` (gain 0 for now) as candidate number *ncand. */
static igraph_error_t overlap_cand_buffer_push(overlap_cand_buffer_t *buffer,
                                               igraph_int_t *ncand, igraph_int_t comm) {
    igraph_int_t needed;

    IGRAPH_SAFE_ADD(*ncand, 1, &needed);
    IGRAPH_CHECK(overlap_cand_buffer_reserve(buffer, needed));
    buffer->data[*ncand].comm = comm;
    buffer->data[*ncand].gain = 0.0;
    *ncand = needed;
    return IGRAPH_SUCCESS;
}

/* ---- Section 4.4.2  Workspace and label bookkeeping ----------------------- */

typedef struct {
    /* Inputs, borrowed from the caller. */
    const igraph_t *graph;
    const igraph_inclist_t *edges_per_node;
    const igraph_vector_t *edge_weights;
    const igraph_vector_t *node_weights;
    igraph_real_t resolution;
    igraph_bool_t allow_isolation;
    igraph_int_t max_memberships;
    igraph_int_t max_total_communities;    /* <= 0: no upper bound */
    igraph_int_t n_communities;            /* <= 0: no exact count */
    igraph_vector_int_list_t *memberships;
    overlap_trace_t *trace;                /* NULL unless diagnostics */

    /* Derived. */
    igraph_bool_t count_constrained;
    /* Omitted labels are needed when isolation is disabled or a count limit
     * applies and gamma * n_v > 0 (one least massive label), or when
     * gamma * n_v < 0 (the most massive ones). Node weights are non-negative,
     * so the sign is the sign of gamma. */
    igraph_bool_t use_label_index;
    igraph_int_t label_bound;              /* n * M: the anonymous label bank */
    igraph_int_t reconcile_period;         /* max(1024, n) queue pops */
    igraph_int_t progress_ceiling;

    /* Labels 0 .. nb_comm_ids - 1; arrays addressable up to cap - 1. */
    igraph_int_t cap;
    igraph_int_t nb_comm_ids;
    igraph_vector_t comm_mass;             /* S_c */
    igraph_vector_int_t comm_tokens;       /* members of each label */
    igraph_stack_int_t empty_comms;        /* recyclable empty label ids */
    igraph_int_t occupied_comms;
    leiden_label_index_t label_index;
    igraph_vector_t inv_sqrt;              /* 1 / sqrt(j), j = 1 .. M */

    /* Per-visit scratch, cleared after every visit. */
    igraph_vector_t edge_w_to_comm;        /* L_v^c */
    igraph_vector_int_t comm_seen;         /* candidate flags */
    overlap_cand_buffer_t cand_buffer;
    igraph_vector_int_t chosen;            /* the new row of a move */

    /* The queue of unstable vertices. */
    igraph_dqueue_int_t unstable_nodes;
    igraph_bitset_t node_is_stable;
    igraph_int_t queue_pop_count;
    igraph_int_t accepted_move_count;
    int interruption_counter;
} overlap_mover_t;

static void overlap_mover_destroy(overlap_mover_t *mover) {
    overlap_cand_buffer_destroy(&mover->cand_buffer);
    igraph_vector_int_destroy(&mover->chosen);
    igraph_dqueue_int_destroy(&mover->unstable_nodes);
    igraph_bitset_destroy(&mover->node_is_stable);
    leiden_label_index_destroy(&mover->label_index);
    igraph_stack_int_destroy(&mover->empty_comms);
    igraph_vector_destroy(&mover->inv_sqrt);
    igraph_vector_int_destroy(&mover->comm_seen);
    igraph_vector_destroy(&mover->edge_w_to_comm);
    igraph_vector_int_destroy(&mover->comm_tokens);
    igraph_vector_destroy(&mover->comm_mass);
}

/* Checks every row size, and finds the number of label ids in use and the
 * maximum degree. Labels must be compact (0 .. nb_comm_ids - 1). */
static igraph_error_t overlap_mover_scan_cover(overlap_mover_t *mover, igraph_int_t *maxdeg) {
    const igraph_int_t n = igraph_vcount(mover->graph);

    *maxdeg = 0;
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(mover->memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);
        const igraph_int_t degree =
            igraph_vector_int_size(igraph_inclist_get(mover->edges_per_node, v));
        if (k < 1 || k > mover->max_memberships) {
            IGRAPH_ERROR("Invalid overlapping membership vector size.", IGRAPH_EINVAL);
        }
        if (degree > *maxdeg) {
            *maxdeg = degree;
        }
        for (igraph_int_t idx = 0; idx < k; idx++) {
            igraph_int_t candidate_id_count;
            IGRAPH_SAFE_ADD(VECTOR(*sigma)[idx], 1, &candidate_id_count);
            if (candidate_id_count > mover->nb_comm_ids) {
                mover->nb_comm_ids = candidate_id_count;
            }
        }
    }
    return IGRAPH_SUCCESS;
}

/* Rebuilds masses, member counts and the empty-label stack from the rows,
 * the authoritative state. Reports whether the incremental state differed
 * beyond the tie margin; with check_drift, debug builds raise an error. */
static igraph_error_t overlap_rebuild_bookkeeping(overlap_mover_t *mover,
                                                  igraph_bool_t check_drift,
                                                  igraph_bool_t *materially_changed) {
    const igraph_int_t cap = igraph_vector_size(&mover->comm_mass);
    const igraph_int_t n = igraph_vector_int_list_size(mover->memberships);
    igraph_vector_t rebuilt_mass;
    igraph_vector_int_t rebuilt_tokens;

    IGRAPH_VECTOR_INIT_FINALLY(&rebuilt_mass, cap);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&rebuilt_tokens, cap);
    igraph_vector_fill(&rebuilt_mass, 0.0);
    igraph_vector_int_fill(&rebuilt_tokens, 0);

    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(mover->memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);
        const igraph_real_t fv = VECTOR(mover->inv_sqrt)[k];
        for (igraph_int_t idx = 0; idx < k; idx++) {
            const igraph_int_t c = VECTOR(*sigma)[idx];
            if (c < 0 || c >= mover->nb_comm_ids || c >= cap) {
                IGRAPH_ERROR("Overlapping Leiden produced an invalid community index.",
                             IGRAPH_EINTERNAL);
            }
            VECTOR(rebuilt_mass)[c] += VECTOR(*mover->node_weights)[v] * fv;
            VECTOR(rebuilt_tokens)[c] += 1;
        }
    }

    *materially_changed = false;
    for (igraph_int_t c = 0; c < mover->nb_comm_ids; c++) {
        const igraph_bool_t mass_moved = !leiden_approximately_equal(
            VECTOR(mover->comm_mass)[c], VECTOR(rebuilt_mass)[c]);
        const igraph_bool_t count_moved =
            VECTOR(mover->comm_tokens)[c] != VECTOR(rebuilt_tokens)[c];
        if (mass_moved || count_moved) {
            *materially_changed = true;
        }
#ifndef NDEBUG
        if (check_drift && mass_moved) {
            IGRAPH_ERRORF("Overlapping Leiden community mass drift at community %" IGRAPH_PRId
                          ": incremental=%g, rebuilt=%g.", IGRAPH_EINTERNAL, c,
                          VECTOR(mover->comm_mass)[c], VECTOR(rebuilt_mass)[c]);
        }
        if (check_drift && count_moved) {
            IGRAPH_ERRORF("Overlapping Leiden community token drift at community %" IGRAPH_PRId
                          ": incremental=%" IGRAPH_PRId ", rebuilt=%" IGRAPH_PRId ".",
                          IGRAPH_EINTERNAL, c, VECTOR(mover->comm_tokens)[c],
                          VECTOR(rebuilt_tokens)[c]);
        }
#else
        (void) check_drift;
#endif
    }

    IGRAPH_CHECK(igraph_vector_update(&mover->comm_mass, &rebuilt_mass));
    IGRAPH_CHECK(igraph_vector_int_update(&mover->comm_tokens, &rebuilt_tokens));
    igraph_stack_int_clear(&mover->empty_comms);
    for (igraph_int_t c = 0; c < mover->nb_comm_ids; c++) {
        if (VECTOR(mover->comm_tokens)[c] == 0) {
            IGRAPH_CHECK(igraph_stack_int_push(&mover->empty_comms, c));
        }
    }

    igraph_vector_int_destroy(&rebuilt_tokens);
    igraph_vector_destroy(&rebuilt_mass);
    IGRAPH_FINALLY_CLEAN(2);
    return IGRAPH_SUCCESS;
}

/* Rebuilds the bookkeeping and the label index. */
static igraph_error_t overlap_mover_reconcile(overlap_mover_t *mover, igraph_bool_t check_drift,
                                              igraph_bool_t *materially_changed) {
    IGRAPH_CHECK(overlap_rebuild_bookkeeping(mover, check_drift, materially_changed));
    if (mover->use_label_index) {
        IGRAPH_CHECK(leiden_label_index_rebuild(&mover->label_index, &mover->comm_tokens,
                                                mover->nb_comm_ids));
    }
    return IGRAPH_SUCCESS;
}

/* Allocates the label arrays (cap entries), 1/sqrt(j), the empty-label
 * stack and the label index, and computes the initial bookkeeping. */
static igraph_error_t overlap_mover_init_labels(overlap_mover_t *mover) {
    igraph_int_t label_storage_bound, inv_sqrt_size;
    igraph_bool_t unused;

    IGRAPH_SAFE_MULT(igraph_vcount(mover->graph), mover->max_memberships, &mover->label_bound);
    IGRAPH_SAFE_ADD(mover->label_bound, 1, &label_storage_bound);
    IGRAPH_SAFE_ADD(mover->nb_comm_ids, 1, &mover->cap);
    if (mover->cap > label_storage_bound) {
        IGRAPH_ERROR("Overlapping Leiden community identifier bound exceeded.",
                     IGRAPH_EOVERFLOW);
    }

    IGRAPH_CHECK(igraph_vector_init(&mover->comm_mass, mover->cap));
    IGRAPH_CHECK(igraph_vector_int_init(&mover->comm_tokens, mover->cap));
    IGRAPH_CHECK(igraph_vector_init(&mover->edge_w_to_comm, mover->cap));
    IGRAPH_CHECK(igraph_vector_int_init(&mover->comm_seen, mover->cap));

    IGRAPH_SAFE_ADD(mover->max_memberships, 1, &inv_sqrt_size);
    IGRAPH_CHECK(igraph_vector_init(&mover->inv_sqrt, inv_sqrt_size));
    for (igraph_int_t j = 1; j <= mover->max_memberships; j++) {
        VECTOR(mover->inv_sqrt)[j] = 1.0 / sqrt((igraph_real_t) j);
    }

    IGRAPH_CHECK(igraph_stack_int_init(&mover->empty_comms, 8));
    IGRAPH_CHECK(leiden_label_index_init(&mover->label_index, &mover->comm_mass,
                                         mover->resolution < 0.0,
                                         mover->use_label_index ? mover->cap : 0));

    IGRAPH_CHECK(overlap_mover_reconcile(mover, false, &unused));
    for (igraph_int_t c = 0; c < mover->nb_comm_ids; c++) {
        if (VECTOR(mover->comm_tokens)[c] > 0) {
            mover->occupied_comms++;
        }
    }
    return IGRAPH_SUCCESS;
}

/* Queues every vertex once, in random order (the only use of the random
 * number generator by overlapping local moving). */
static igraph_error_t overlap_mover_init_queue(overlap_mover_t *mover) {
    const igraph_int_t n = igraph_vcount(mover->graph);
    igraph_vector_int_t node_order;

    IGRAPH_CHECK(igraph_bitset_init(&mover->node_is_stable, n));
    IGRAPH_CHECK(igraph_dqueue_int_init(&mover->unstable_nodes, n));
    IGRAPH_CHECK(igraph_vector_int_init_range(&node_order, 0, n));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &node_order);
    igraph_vector_int_shuffle(&node_order);
    for (igraph_int_t i = 0; i < n; i++) {
        IGRAPH_CHECK(igraph_dqueue_int_push(&mover->unstable_nodes, VECTOR(node_order)[i]));
    }
    igraph_vector_int_destroy(&node_order);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* Candidates per visit: own labels, neighbour labels, one empty label and
 * the omitted labels (one, or M plus rounding ties). The buffer starts at
 * min(256, maxdeg * M + M + 2). */
static igraph_error_t overlap_mover_init_candidates(overlap_mover_t *mover, igraph_int_t maxdeg) {
    igraph_int_t neighbour_cand_bound;

    IGRAPH_CHECK(igraph_vector_int_init(&mover->chosen, mover->max_memberships));
    IGRAPH_SAFE_MULT(maxdeg, mover->max_memberships, &neighbour_cand_bound);
    IGRAPH_SAFE_ADD(neighbour_cand_bound, mover->max_memberships, &neighbour_cand_bound);
    IGRAPH_SAFE_ADD(neighbour_cand_bound, 2, &neighbour_cand_bound);
    IGRAPH_CHECK(overlap_cand_buffer_reserve(&mover->cand_buffer,
                                             neighbour_cand_bound < 256 ? neighbour_cand_bound : 256));
    return IGRAPH_SUCCESS;
}

/* Grows the label arrays so that ids below `needed` are addressable; new
 * entries are empty labels. */
static igraph_error_t overlap_mover_ensure_capacity(overlap_mover_t *mover, igraph_int_t needed) {
    igraph_int_t newcap;

    if (needed <= mover->cap) {
        return IGRAPH_SUCCESS;
    }
    newcap = mover->cap > IGRAPH_INTEGER_MAX / 2 ? IGRAPH_INTEGER_MAX : 2 * mover->cap;
    if (newcap < needed) {
        newcap = needed;
    }
    IGRAPH_CHECK(igraph_vector_resize(&mover->comm_mass, newcap));
    IGRAPH_CHECK(igraph_vector_int_resize(&mover->comm_tokens, newcap));
    IGRAPH_CHECK(igraph_vector_resize(&mover->edge_w_to_comm, newcap));
    IGRAPH_CHECK(igraph_vector_int_resize(&mover->comm_seen, newcap));
    for (igraph_int_t c = mover->cap; c < newcap; c++) {
        VECTOR(mover->comm_mass)[c] = 0.0;
        VECTOR(mover->comm_tokens)[c] = 0;
        VECTOR(mover->edge_w_to_comm)[c] = 0.0;
        VECTOR(mover->comm_seen)[c] = 0;
    }
    mover->cap = newcap;
    return IGRAPH_SUCCESS;
}

/* The overlapping analogue of leiden_options_t, for one run (Section 4.9). */
typedef struct {
    const igraph_t *graph;
    igraph_vector_t *edge_weights;        /* never NULL */
    igraph_vector_t *node_weights;        /* never NULL */
    igraph_real_t resolution;
    igraph_real_t beta;
    igraph_int_t max_memberships;
    igraph_int_t max_total_communities;   /* <= 0: no upper bound */
    igraph_int_t n_communities;           /* <= 0: no exact count */
    igraph_bool_t allow_isolation;
    igraph_bool_t local_move_only;
    igraph_vector_int_list_t *memberships;
    overlap_trace_t *trace;               /* NULL unless diagnostics */
    igraph_matrix_t *projection_trace;    /* NULL unless diagnostics */
} overlap_run_t;

/* Prepares overlapping local moving of run->memberships. The caller has
 * zero-initialized `mover` and registered overlap_mover_destroy. */
static igraph_error_t overlap_mover_init(overlap_mover_t *mover, const overlap_run_t *run,
                                         const igraph_inclist_t *edges_per_node) {
    const igraph_int_t n = igraph_vcount(run->graph);
    igraph_int_t maxdeg;

    mover->graph = run->graph;
    mover->edges_per_node = edges_per_node;
    mover->edge_weights = run->edge_weights;
    mover->node_weights = run->node_weights;
    mover->resolution = run->resolution;
    mover->allow_isolation = run->allow_isolation;
    mover->max_memberships = run->max_memberships;
    mover->max_total_communities = run->max_total_communities;
    mover->n_communities = run->n_communities;
    mover->memberships = run->memberships;
    mover->trace = run->trace;
    mover->count_constrained = run->max_total_communities > 0 || run->n_communities > 0;
    mover->use_label_index = run->resolution < 0.0 ||
        ((!run->allow_isolation || mover->count_constrained) && run->resolution > 0.0);
    /* A rebuild costs O(sum_v k_v + #labels); every n pops (at least every
     * 1024) keeps its amortized cost at O(k_bar + #labels / n) per pop. */
    mover->reconcile_period = n > 1024 ? n : 1024;
    mover->progress_ceiling = leiden_progress_ceiling(n, run->max_memberships);

    IGRAPH_CHECK(overlap_mover_scan_cover(mover, &maxdeg));
    IGRAPH_CHECK(overlap_mover_init_labels(mover));
    IGRAPH_CHECK(overlap_mover_init_queue(mover));
    IGRAPH_CHECK(overlap_mover_init_candidates(mover, maxdeg));
    return IGRAPH_SUCCESS;
}

/* ---- Section 4.4.3  Candidate labels of one vertex ------------------------ */

/* The state of one visit. */
typedef struct {
    igraph_int_t v;
    igraph_vector_int_t *sigma;   /* v's current row */
    igraph_int_t k;               /* |sigma| */
    igraph_real_t nv;             /* n_v */
    igraph_real_t fv;             /* 1 / sqrt(k) */
    igraph_int_t empty_c;         /* the offered empty label, or -1 */
    igraph_int_t ncand;           /* candidates collected */
    igraph_int_t mandatory;       /* leading candidates that must be kept */
    igraph_int_t jmax;            /* longest prefix worth scoring */
    igraph_real_t cur_score;      /* U_v of the current row */
    igraph_real_t best_score;
    igraph_int_t best_j;          /* best prefix length; 0 if none improves */
} overlap_visit_t;

static void overlap_visit_begin(const overlap_mover_t *mover, igraph_int_t v,
                                overlap_visit_t *visit) {
    visit->v = v;
    visit->sigma = igraph_vector_int_list_get_ptr(mover->memberships, v);
    visit->k = igraph_vector_int_size(visit->sigma);
    visit->nv = VECTOR(*mover->node_weights)[v];
    visit->fv = VECTOR(mover->inv_sqrt)[visit->k];
    visit->empty_c = -1;
    visit->ncand = 0;
    visit->mandatory = 0;
    visit->jmax = 0;
    visit->cur_score = 0.0;
    visit->best_score = 0.0;
    visit->best_j = 0;
}

static igraph_error_t overlap_add_candidate(overlap_mover_t *mover, overlap_visit_t *visit,
                                           igraph_int_t c) {
    VECTOR(mover->comm_seen)[c] = 1;
    return overlap_cand_buffer_push(&mover->cand_buffer, &visit->ncand, c);
}

/* Reserves a recyclable empty label for v when one may be offered: with
 * isolation allowed, no exact count, and an upper bound not yet reached.
 * A new id is taken from the label bank if no empty label is left. */
static igraph_error_t overlap_offer_empty_label(overlap_mover_t *mover, overlap_visit_t *visit) {
    if (!(mover->allow_isolation && mover->n_communities <= 0 &&
          (mover->max_total_communities <= 0 ||
           mover->occupied_comms < mover->max_total_communities))) {
        return IGRAPH_SUCCESS;
    }
    if (igraph_stack_int_empty(&mover->empty_comms)) {
        igraph_int_t needed;
        IGRAPH_SAFE_ADD(mover->nb_comm_ids, 1, &needed);
        if (needed > mover->label_bound) {
            IGRAPH_ERROR("Overlapping Leiden exhausted its finite label bound.",
                         IGRAPH_EOVERFLOW);
        }
        IGRAPH_CHECK(overlap_mover_ensure_capacity(mover, needed));
        IGRAPH_CHECK(igraph_stack_int_push(&mover->empty_comms, mover->nb_comm_ids));
        mover->nb_comm_ids++;
    }
    visit->empty_c = igraph_stack_int_top(&mover->empty_comms);
    return IGRAPH_SUCCESS;
}

/* v's own labels come first (candidates 0 .. k - 1); the gain correction
 * in Section 4.4.4 relies on this order. */
static igraph_error_t overlap_collect_own_labels(overlap_mover_t *mover, overlap_visit_t *visit) {
    for (igraph_int_t idx = 0; idx < visit->k; idx++) {
        IGRAPH_CHECK(overlap_add_candidate(mover, visit, VECTOR(*visit->sigma)[idx]));
    }
    return IGRAPH_SUCCESS;
}

/* Adds the labels of v's neighbours and accumulates L_v^c. */
static igraph_error_t overlap_collect_neighbour_labels(overlap_mover_t *mover,
                                                       overlap_visit_t *visit) {
    const igraph_int_t v = visit->v;
    const igraph_vector_int_t *edges = igraph_inclist_get(mover->edges_per_node, v);
    const igraph_int_t degree = igraph_vector_int_size(edges);

    for (igraph_int_t i = 0; i < degree; i++) {
        const igraph_int_t e = VECTOR(*edges)[i];
        const igraph_int_t u = IGRAPH_OTHER(mover->graph, e, v);
        const igraph_vector_int_t *sigma_u;
        igraph_int_t ku;
        igraph_real_t wf;
        if (u == v) {
            continue;
        }
        sigma_u = igraph_vector_int_list_get_ptr(mover->memberships, u);
        ku = igraph_vector_int_size(sigma_u);
        wf = VECTOR(*mover->edge_weights)[e] * VECTOR(mover->inv_sqrt)[ku];
        for (igraph_int_t idx = 0; idx < ku; idx++) {
            const igraph_int_t c = VECTOR(*sigma_u)[idx];
            if (!VECTOR(mover->comm_seen)[c]) {
                IGRAPH_CHECK(overlap_add_candidate(mover, visit, c));
            }
            VECTOR(mover->edge_w_to_comm)[c] += wf;
        }
    }
    return IGRAPH_SUCCESS;
}

static igraph_error_t overlap_collect_empty_label(overlap_mover_t *mover, overlap_visit_t *visit) {
    if (visit->empty_c >= 0 && !VECTOR(mover->comm_seen)[visit->empty_c]) {
        IGRAPH_CHECK(overlap_add_candidate(mover, visit, visit->empty_c));
    }
    return IGRAPH_SUCCESS;
}

/* Must omitted labels complete the candidate set? The empty label (gain 0)
 * dominates them only when isolation is allowed and gamma * n_v >= 0. When a
 * count limit withholds the empty label and gamma * n_v > 0, a label held by
 * v alone has the same zero gain and also dominates them; without one, the
 * least massive omitted label is needed. */
static igraph_bool_t overlap_needs_omitted_labels(const overlap_mover_t *mover,
                                                  const overlap_visit_t *visit) {
    const igraph_real_t signed_scale = mover->resolution * visit->nv;

    if (!mover->allow_isolation || signed_scale < 0.0) {
        return true;
    }
    if (mover->count_constrained && visit->empty_c < 0 && signed_scale > 0.0) {
        for (igraph_int_t idx = 0; idx < visit->k; idx++) {
            if (VECTOR(mover->comm_tokens)[VECTOR(*visit->sigma)[idx]] == 1) {
                return false;
            }
        }
        return true;
    }
    return false;
}

#ifndef NDEBUG
/* Debug oracle for the label index: among occupied labels that are not yet
 * candidates, the one extremizing -gamma * n_v * S_c (lowest id on ties), or
 * -1. */
static igraph_int_t overlap_find_omitted_extreme_label(const overlap_mover_t *mover,
                                                       igraph_real_t node_weight) {
    const igraph_real_t signed_scale = mover->resolution * node_weight;
    const igraph_bool_t want_min = (signed_scale > 0.0);
    igraph_int_t best = -1;
    igraph_real_t best_mass = 0.0;

    if (signed_scale == 0.0) {
        return -1;
    }
    for (igraph_int_t c = 0; c < mover->nb_comm_ids; c++) {
        igraph_real_t mass;

        if (VECTOR(mover->comm_tokens)[c] <= 0 || VECTOR(mover->comm_seen)[c]) {
            continue;
        }
        mass = VECTOR(mover->comm_mass)[c];
        if (best < 0 ||
            (want_min ? (mass < best_mass || (mass == best_mass && c < best))
                      : (mass > best_mass || (mass == best_mass && c < best)))) {
            best = c;
            best_mass = mass;
        }
    }
    return best;
}
#endif

/* gamma * n_v > 0: adds the least massive omitted label. */
static igraph_error_t overlap_add_least_massive_omitted(overlap_mover_t *mover,
                                                        overlap_visit_t *visit) {
    igraph_int_t omitted;

    IGRAPH_CHECK(leiden_label_index_begin(&mover->label_index));
    IGRAPH_CHECK(leiden_label_index_next(&mover->label_index, &mover->comm_seen, NULL, &omitted));
#ifndef NDEBUG
    if (omitted != overlap_find_omitted_extreme_label(mover, visit->nv)) {
        IGRAPH_ERROR("Overlapping Leiden label index disagrees with the "
                     "omitted-label scan.", IGRAPH_EINTERNAL);
    }
#endif
    if (omitted >= 0) {
        IGRAPH_CHECK(overlap_add_candidate(mover, visit, omitted));
    }
    return IGRAPH_SUCCESS;
}

/* gamma * n_v < 0: omitted gains -gamma * n_v * S_c are positive and do not
 * increase along the index order, so the labels that can occupy the first M
 * sorted positions are the first M in that order plus any label whose
 * computed gain ties the last one (rounding can merge distinct masses). */
static igraph_error_t overlap_add_most_massive_omitted(overlap_mover_t *mover,
                                                       overlap_visit_t *visit) {
    igraph_int_t taken = 0, omitted;
    igraph_real_t last_gain = 0.0;

    IGRAPH_CHECK(leiden_label_index_begin(&mover->label_index));
    for (;;) {
        igraph_real_t gain;
        IGRAPH_CHECK(leiden_label_index_next(&mover->label_index, &mover->comm_seen, NULL,
                                             &omitted));
        if (omitted < 0) {
            break;
        }
        /* The expression of Section 4.4.4, whose support term is zero here. */
        gain = 0.0 - mover->resolution * visit->nv * VECTOR(mover->comm_mass)[omitted];
        if (taken >= mover->max_memberships && gain != last_gain) {
            break;
        }
        IGRAPH_CHECK(overlap_add_candidate(mover, visit, omitted));
        taken++;
        last_gain = gain;
    }
#ifndef NDEBUG
    /* Oracle: every omitted label left out ranks strictly after the block. */
    for (igraph_int_t c = 0; c < mover->nb_comm_ids; c++) {
        if (VECTOR(mover->comm_tokens)[c] > 0 && !VECTOR(mover->comm_seen)[c] &&
            (taken < mover->max_memberships ||
             !(0.0 - mover->resolution * visit->nv * VECTOR(mover->comm_mass)[c] < last_gain))) {
            IGRAPH_ERROR("Overlapping Leiden label index omitted a label that "
                         "can enter a best response.", IGRAPH_EINTERNAL);
        }
    }
#endif
    return IGRAPH_SUCCESS;
}

/* Completes the non-neighbour class of candidates when needed. */
static igraph_error_t overlap_complete_omitted_labels(overlap_mover_t *mover,
                                                      overlap_visit_t *visit) {
    const igraph_real_t signed_scale = mover->resolution * visit->nv;

    if (!overlap_needs_omitted_labels(mover, visit)) {
        return IGRAPH_SUCCESS;
    }
    if (signed_scale > 0.0) {
        return overlap_add_least_massive_omitted(mover, visit);
    }
    if (signed_scale < 0.0) {
        return overlap_add_most_massive_omitted(mover, visit);
    }
    return IGRAPH_SUCCESS;
}

/* Collects all candidate labels of v, in this order: own labels, neighbour
 * labels, the empty label, omitted labels. */
static igraph_error_t overlap_collect_candidates(overlap_mover_t *mover, overlap_visit_t *visit) {
    IGRAPH_CHECK(overlap_offer_empty_label(mover, visit));
    IGRAPH_CHECK(overlap_collect_own_labels(mover, visit));
    IGRAPH_CHECK(overlap_collect_neighbour_labels(mover, visit));
    IGRAPH_CHECK(overlap_collect_empty_label(mover, visit));
    IGRAPH_CHECK(overlap_complete_omitted_labels(mover, visit));
    return IGRAPH_SUCCESS;
}

/* ---- Section 4.4.4  Gains and the current score --------------------------- */

/* g_c = L_v^c - gamma n_v S_c for every candidate; clears the scratch. */
static void overlap_compute_gains(overlap_mover_t *mover, overlap_visit_t *visit) {
    overlap_cand_t *cand = mover->cand_buffer.data;

    for (igraph_int_t i = 0; i < visit->ncand; i++) {
        const igraph_int_t c = cand[i].comm;
        cand[i].gain = VECTOR(mover->edge_w_to_comm)[c]
                       - mover->resolution * visit->nv * VECTOR(mover->comm_mass)[c];
        VECTOR(mover->edge_w_to_comm)[c] = 0.0;
        VECTOR(mover->comm_seen)[c] = 0;
    }
}

/* v's own labels still count v's mass in S_c: adding it back turns their
 * gains into g_c = L_v^c - gamma n_v W_v^c. Their sum times f_v is v's
 * current contribution U_v (up to the constant self term). */
static void overlap_score_current_row(overlap_mover_t *mover, overlap_visit_t *visit) {
    overlap_cand_t *cand = mover->cand_buffer.data;

    for (igraph_int_t i = 0; i < visit->k; i++) {
        cand[i].gain += mover->resolution * visit->nv * visit->nv * visit->fv;
        /* An exclusive label has no other mass or edge support. Avoid a
         * cancellation residual in the current score before the mandatory
         * prefix is formed; with large node weights it can hide real moves. */
        if (VECTOR(mover->comm_tokens)[cand[i].comm] == 1) {
            cand[i].gain = 0.0;
        }
        visit->cur_score += cand[i].gain;
    }
    visit->cur_score *= visit->fv;
}

/* ---- Section 4.4.5  Sorted-prefix best response --------------------------- */

/* With an exact count, a label held by v alone cannot be dropped (it would
 * empty the label). Moves such mandatory labels to the front, recording
 * their gain as exactly zero (no other vertex supports it or carries its
 * mass). Returns their number. */
static igraph_int_t overlap_front_mandatory_labels(const overlap_mover_t *mover,
                                                   const overlap_visit_t *visit) {
    overlap_cand_t *cand = mover->cand_buffer.data;
    igraph_int_t mandatory = 0;

    if (mover->n_communities <= 0) {
        return 0;
    }
    for (igraph_int_t i = 0; i < visit->k; i++) {
        if (VECTOR(mover->comm_tokens)[cand[i].comm] == 1) {
            overlap_cand_swap(cand, mandatory, i);
            cand[mandatory].gain = 0.0;
            mandatory++;
        }
    }
    return mandatory;
}

/* Moves the positive-gain optional candidates right after the mandatory
 * ones; if nothing ends up in front, the single best candidate. Returns the
 * end of that front block.
 *
 * Why this suffices: appending a non-positive gain g to a prefix with
 * positive sum P never raises P / sqrt(j) (P + g <= P while the divisor
 * grows; rounding is monotone), so every prefix that extends past the
 * positive block is dominated. If no gain is positive, a j-set scores at most
 * sqrt(j) g_(1) <= g_(1), so the best single candidate is the best response.
 * Sorting only the front block therefore selects the same response as
 * sorting all candidates. */
static igraph_int_t overlap_front_positive_gains(const overlap_mover_t *mover,
                                                 const overlap_visit_t *visit) {
    overlap_cand_t *cand = mover->cand_buffer.data;
    igraph_int_t npos = visit->mandatory;

    for (igraph_int_t i = visit->mandatory; i < visit->ncand; i++) {
        if (cand[i].gain > 0.0) {
            overlap_cand_swap(cand, npos, i);
            npos++;
        }
    }
    if (npos == 0 && visit->ncand > 0) {
        igraph_int_t best_i = 0;
        for (igraph_int_t i = 1; i < visit->ncand; i++) {
            if (overlap_cand_cmp(&cand[i], &cand[best_i]) < 0) {
                best_i = i;
            }
        }
        overlap_cand_swap(cand, 0, best_i);
        npos = 1;
    }
    return npos;
}

/* Orders the candidates for the prefix scan: mandatory labels, then the
 * sorted front block. Sets visit->mandatory and visit->jmax. */
static void overlap_order_candidates(overlap_mover_t *mover, overlap_visit_t *visit) {
    overlap_cand_t *cand = mover->cand_buffer.data;
    igraph_int_t npos;

    visit->mandatory = overlap_front_mandatory_labels(mover, visit);
    npos = overlap_front_positive_gains(mover, visit);
    qsort(cand + visit->mandatory, (size_t) (npos - visit->mandatory), sizeof(*cand),
          overlap_cand_cmp);
    visit->jmax = npos < mover->max_memberships ? npos : mover->max_memberships;
}

/* The prefix of length j (mandatory <= j <= jmax) maximizing
 * (sum of its gains) / sqrt(j), if it beats the current score by more than
 * the tie margin. */
static void overlap_best_prefix(const overlap_mover_t *mover, overlap_visit_t *visit) {
    const overlap_cand_t *cand = mover->cand_buffer.data;
    igraph_real_t prefix = 0.0;

    visit->best_score = visit->cur_score;
    visit->best_j = 0;
    for (igraph_int_t j = 1; j <= visit->jmax; j++) {
        igraph_real_t score;
        prefix += cand[j - 1].gain;
        if (j < visit->mandatory) {
            continue;
        }
        score = prefix * VECTOR(mover->inv_sqrt)[j];
        if (leiden_is_improvement(score, visit->best_score)) {
            visit->best_score = score;
            visit->best_j = j;
        }
    }
}

/* ---- Section 4.4.6  Applying a move --------------------------------------- */

/* Writes the best prefix, sorted, into mover->chosen. Returns whether it
 * uses the offered empty label. */
static igraph_error_t overlap_fill_chosen_row(overlap_mover_t *mover, const overlap_visit_t *visit,
                                              igraph_bool_t *used_empty) {
    const overlap_cand_t *cand = mover->cand_buffer.data;

    *used_empty = false;
    IGRAPH_CHECK(igraph_vector_int_resize(&mover->chosen, visit->best_j));
    for (igraph_int_t j = 0; j < visit->best_j; j++) {
        VECTOR(mover->chosen)[j] = cand[j].comm;
        if (cand[j].comm == visit->empty_c) {
            *used_empty = true;
        }
    }
    igraph_vector_int_sort(&mover->chosen);
    return IGRAPH_SUCCESS;
}

/* Is the chosen row identical to v's row? (Summation-order differences
 * between the current score and the prefix sums can make the same row
 * look like an improvement.) */
static igraph_bool_t overlap_row_unchanged(const overlap_mover_t *mover,
                                           const overlap_visit_t *visit) {
    if (visit->best_j != visit->k) {
        return false;
    }
    for (igraph_int_t j = 0; j < visit->best_j; j++) {
        if (VECTOR(mover->chosen)[j] != VECTOR(*visit->sigma)[j]) {
            return false;
        }
    }
    return true;
}

/* v leaves label c: S_c loses n_v f_old; an emptied label becomes
 * recyclable. */
static igraph_error_t overlap_label_leave(overlap_mover_t *mover, igraph_int_t c,
                                          igraph_real_t nv, igraph_real_t fv) {
    VECTOR(mover->comm_mass)[c] -= nv * fv;
    VECTOR(mover->comm_tokens)[c] -= 1;
    if (VECTOR(mover->comm_tokens)[c] == 0) {
        VECTOR(mover->comm_mass)[c] = 0.0;
        mover->occupied_comms--;
        IGRAPH_CHECK(igraph_stack_int_push(&mover->empty_comms, c));
        if (mover->use_label_index) {
            leiden_label_index_remove(&mover->label_index, c);
        }
    } else if (mover->use_label_index) {
        leiden_label_index_update(&mover->label_index, c);
    }
    return IGRAPH_SUCCESS;
}

/* v joins label c: S_c gains n_v f_new. */
static igraph_error_t overlap_label_join(overlap_mover_t *mover, igraph_int_t c,
                                         igraph_real_t nv, igraph_real_t fnew) {
    VECTOR(mover->comm_mass)[c] += nv * fnew;
    VECTOR(mover->comm_tokens)[c] += 1;
    if (VECTOR(mover->comm_tokens)[c] == 1) {
        mover->occupied_comms++;
    }
    if (mover->use_label_index) {
        if (VECTOR(mover->comm_tokens)[c] == 1) {
            IGRAPH_CHECK(leiden_label_index_insert(&mover->label_index, c));
        } else {
            leiden_label_index_update(&mover->label_index, c);
        }
    }
    return IGRAPH_SUCCESS;
}

/* v keeps label c with a new intensity: S_c changes by n_v (f_new - f_old). */
static void overlap_label_rescale(overlap_mover_t *mover, igraph_int_t c,
                                  igraph_real_t nv, igraph_real_t fnew, igraph_real_t fv) {
    VECTOR(mover->comm_mass)[c] += nv * (fnew - fv);
    if (mover->use_label_index) {
        leiden_label_index_update(&mover->label_index, c);
    }
}

/* Updates the label bookkeeping for the change from sigma to chosen by
 * merging the two sorted rows. */
static igraph_error_t overlap_update_labels(overlap_mover_t *mover, const overlap_visit_t *visit) {
    const igraph_vector_int_t *sigma = visit->sigma;
    const igraph_vector_int_t *chosen = &mover->chosen;
    const igraph_int_t k = visit->k, best_j = visit->best_j;
    const igraph_real_t fnew = VECTOR(mover->inv_sqrt)[best_j];
    igraph_int_t ia = 0, ib = 0;

    while (ia < k || ib < best_j) {
        if (ib >= best_j || (ia < k && VECTOR(*sigma)[ia] < VECTOR(*chosen)[ib])) {
            IGRAPH_CHECK(overlap_label_leave(mover, VECTOR(*sigma)[ia++], visit->nv, visit->fv));
        } else if (ia >= k || VECTOR(*chosen)[ib] < VECTOR(*sigma)[ia]) {
            IGRAPH_CHECK(overlap_label_join(mover, VECTOR(*chosen)[ib++], visit->nv, fnew));
        } else {
            overlap_label_rescale(mover, VECTOR(*sigma)[ia], visit->nv, fnew, visit->fv);
            ia++;
            ib++;
        }
    }
    return IGRAPH_SUCCESS;
}

/* A changed row can alter the best response of any neighbour: re-queue the
 * stable ones. */
static igraph_error_t overlap_requeue_neighbours(overlap_mover_t *mover, igraph_int_t v) {
    const igraph_vector_int_t *edges = igraph_inclist_get(mover->edges_per_node, v);
    const igraph_int_t degree = igraph_vector_int_size(edges);

    for (igraph_int_t i = 0; i < degree; i++) {
        const igraph_int_t e = VECTOR(*edges)[i];
        const igraph_int_t u = IGRAPH_OTHER(mover->graph, e, v);
        if (u != v && IGRAPH_BIT_TEST(mover->node_is_stable, u)) {
            IGRAPH_CHECK(igraph_dqueue_int_push(&mover->unstable_nodes, u));
            IGRAPH_BIT_CLEAR(mover->node_is_stable, u);
        }
    }
    return IGRAPH_SUCCESS;
}

/* Raises an internal error once the progress ceiling is reached. */
static igraph_error_t overlap_check_progress(const overlap_mover_t *mover) {
    if (mover->queue_pop_count >= mover->progress_ceiling ||
        mover->accepted_move_count >= mover->progress_ceiling) {
        const igraph_uint_t membership_hash = overlap_cover_hash(mover->memberships);
        IGRAPH_ERRORF("Overlapping Leiden progress ceiling reached (accepted moves=%" IGRAPH_PRId
                      ", queue pops=%" IGRAPH_PRId ", membership hash=%" IGRAPH_PRIu ").",
                      IGRAPH_EINTERNAL, mover->accepted_move_count, mover->queue_pop_count,
                      membership_hash);
    }
    return IGRAPH_SUCCESS;
}

/* ---- Section 4.4.7  Accepted-move trace ----------------------------------- */

/* The quality before a move, recomputed directly (diagnostics only). */
typedef struct {
    igraph_real_t quality;
    igraph_real_t magnitude;
    igraph_int_t terms;
} overlap_trace_sample_t;

static igraph_bool_t overlap_tracing_moves(const overlap_mover_t *mover) {
    return mover->trace && mover->trace->move_trace;
}

static igraph_error_t overlap_trace_sample(const overlap_mover_t *mover,
                                           overlap_trace_sample_t *sample) {
    return overlap_quality_ext(mover->graph, mover->edge_weights, mover->node_weights,
                               mover->memberships, mover->resolution, &sample->quality,
                               &sample->magnitude, &sample->terms);
}

/* Compares the mover's predicted potential change with a direct
 * recomputation, raises an error if they disagree beyond the rounding bound,
 * and appends one row to the move trace. The direct change differences two
 * recomputed sums of O(m + #labels) terms, so the bound adds their
 * recursive-summation error to the tie margin of the prediction. */
static igraph_error_t overlap_trace_record_move(overlap_mover_t *mover,
                                                const overlap_visit_t *visit,
                                                const overlap_trace_sample_t *before) {
    overlap_trace_t *trace = mover->trace;
    const igraph_real_t predicted_delta = visit->best_score - visit->cur_score;
    overlap_trace_sample_t after;
    igraph_real_t direct_delta, error, tolerance;
    igraph_real_t values[IGRAPH_LEIDEN_OVERLAP_MOVE_TRACE_WIDTH];

    IGRAPH_CHECK(overlap_trace_sample(mover, &after));
    direct_delta = (after.quality - before->quality) * trace->original_weight;
    error = fabs(predicted_delta - direct_delta);
    tolerance = leiden_tolerance(predicted_delta, direct_delta) +
        DBL_EPSILON * ((igraph_real_t) before->terms * before->magnitude +
                       (igraph_real_t) after.terms * after.magnitude);
    if (error > tolerance) {
        IGRAPH_ERRORF("Overlapping Leiden accepted-move delta mismatch "
                      "(predicted=%g, direct=%g, tolerance=%g).",
                      IGRAPH_EINTERNAL, predicted_delta, direct_delta, tolerance);
    }
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_SEQUENCE] = trace->move_sequence;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_STAGE] = trace->stage;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_VERTEX] = visit->v;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_CARDINALITY_BEFORE] = visit->k;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_CARDINALITY_AFTER] = visit->best_j;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_PREDICTED_DELTA] = predicted_delta;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_DIRECT_DELTA] = direct_delta;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_ABS_ERROR] = error;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_TOLERANCE] = tolerance;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_QUALITY_BEFORE] = before->quality;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_QUALITY_AFTER] = after.quality;
    values[IGRAPH_LEIDEN_OVERLAP_MOVE_ORIGINAL_WEIGHT] = trace->original_weight;
    IGRAPH_CHECK(overlap_trace_append(trace->move_trace, values,
                                      IGRAPH_LEIDEN_OVERLAP_MOVE_TRACE_WIDTH));
    trace->move_sequence++;
    return IGRAPH_SUCCESS;
}

/* Replaces v's row by the chosen one: bookkeeping, row, trace, queue. */
static igraph_error_t overlap_apply_move(overlap_mover_t *mover, const overlap_visit_t *visit,
                                         igraph_bool_t used_empty, igraph_bool_t *changed) {
    overlap_trace_sample_t before = { 0.0, 0.0, 0 };

    if (overlap_tracing_moves(mover)) {
        IGRAPH_CHECK(overlap_trace_sample(mover, &before));
    }
    *changed = true;
    mover->accepted_move_count++;

    /* Pop the empty label before any push can bury it. */
    if (used_empty) {
        igraph_stack_int_pop(&mover->empty_comms);
    }
    IGRAPH_CHECK(overlap_update_labels(mover, visit));
    IGRAPH_CHECK(igraph_vector_int_update(visit->sigma, &mover->chosen));

    if (overlap_tracing_moves(mover)) {
        IGRAPH_CHECK(overlap_trace_record_move(mover, visit, &before));
    }
    IGRAPH_CHECK(overlap_requeue_neighbours(mover, visit->v));
    if (mover->accepted_move_count >= mover->progress_ceiling) {
        IGRAPH_CHECK(overlap_check_progress(mover));
    }
    return IGRAPH_SUCCESS;
}

/* Adopts the best prefix if there is one and it differs from v's row. */
static igraph_error_t overlap_adopt_best_response(overlap_mover_t *mover,
                                                  const overlap_visit_t *visit,
                                                  igraph_bool_t *changed) {
    igraph_bool_t used_empty;

    if (visit->best_j == 0) {
        return IGRAPH_SUCCESS;
    }
    IGRAPH_CHECK(overlap_fill_chosen_row(mover, visit, &used_empty));
    if (overlap_row_unchanged(mover, visit)) {
        return IGRAPH_SUCCESS;
    }
    return overlap_apply_move(mover, visit, used_empty, changed);
}

/* ---- Section 4.4.8  The queue loop ---------------------------------------- */

/* Re-queues every vertex in id order (after a material correction). */
static igraph_error_t overlap_mover_requeue_all(overlap_mover_t *mover) {
    const igraph_int_t n = igraph_vcount(mover->graph);

    igraph_bitset_fill(&mover->node_is_stable, false);
    igraph_dqueue_int_clear(&mover->unstable_nodes);
    for (igraph_int_t i = 0; i < n; i++) {
        IGRAPH_CHECK(igraph_dqueue_int_push(&mover->unstable_nodes, i));
    }
    return IGRAPH_SUCCESS;
}

/* Pops the next vertex, enforcing the progress ceiling and reconciling the
 * bookkeeping every reconcile_period pops. */
static igraph_error_t overlap_mover_next_vertex(overlap_mover_t *mover, igraph_int_t *v) {
    IGRAPH_CHECK(overlap_check_progress(mover));
    *v = igraph_dqueue_int_pop(&mover->unstable_nodes);
    mover->queue_pop_count++;
    if (mover->queue_pop_count % mover->reconcile_period == 0) {
        igraph_bool_t corrected;
        IGRAPH_CHECK(overlap_mover_reconcile(mover, true, &corrected));
        if (corrected) {
            /* A corrected mass state invalidates every stability decision. */
            IGRAPH_CHECK(overlap_mover_requeue_all(mover));
        }
    }
    return IGRAPH_SUCCESS;
}

/* Visits vertex v: computes its best-response set and adopts it if it
 * improves v's score beyond the tie margin. */
static igraph_error_t overlap_mover_visit(overlap_mover_t *mover, igraph_int_t v,
                                          igraph_bool_t *changed) {
    overlap_visit_t visit;

    overlap_visit_begin(mover, v, &visit);
    IGRAPH_CHECK(overlap_collect_candidates(mover, &visit));
    overlap_compute_gains(mover, &visit);
    overlap_score_current_row(mover, &visit);
    overlap_order_candidates(mover, &visit);
    overlap_best_prefix(mover, &visit);
    IGRAPH_CHECK(overlap_adopt_best_response(mover, &visit, changed));
    IGRAPH_BIT_SET(mover->node_is_stable, v);
    return IGRAPH_SUCCESS;
}

/* After the loop: debug builds re-check the bookkeeping, and the count
 * limits must hold. */
static igraph_error_t overlap_mover_finish(overlap_mover_t *mover) {
#ifndef NDEBUG
    igraph_bool_t unused;
    IGRAPH_CHECK(overlap_rebuild_bookkeeping(mover, true, &unused));
#endif
    if ((mover->max_total_communities > 0 &&
         mover->occupied_comms > mover->max_total_communities) ||
        (mover->n_communities > 0 && mover->occupied_comms != mover->n_communities)) {
        IGRAPH_ERROR("Overlapping Leiden local moving violated a community-count constraint.",
                     IGRAPH_EINTERNAL);
    }
    return IGRAPH_SUCCESS;
}

/* Overlapping local moving (phase 1) of run->memberships, which must be
 * compact. Sets *changed if any row changed. */
static igraph_error_t overlap_fastmove_nodes(const overlap_run_t *run,
                                             const igraph_inclist_t *edges_per_node,
                                             igraph_bool_t *changed) {
    overlap_mover_t mover = { .graph = NULL };

    IGRAPH_FINALLY(overlap_mover_destroy, &mover);
    IGRAPH_CHECK(overlap_mover_init(&mover, run, edges_per_node));
    while (!igraph_dqueue_int_empty(&mover.unstable_nodes)) {
        igraph_int_t v;
        IGRAPH_CHECK(overlap_mover_next_vertex(&mover, &v));
        IGRAPH_CHECK(overlap_mover_visit(&mover, v, changed));
        IGRAPH_CHECK(leiden_check_interruption(&mover.interruption_counter, 1 << 13));
    }
    IGRAPH_CHECK(overlap_mover_finish(&mover));
    overlap_mover_destroy(&mover);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}


/* -----------------------------------------------------------------------------
 * Section 4.5  Token graph and projection
 * -----------------------------------------------------------------------------
 *
 * The token graph has one vertex per (vertex v, label c in sigma_v) pair,
 * with vertex weight n_v / sqrt(k_v), and, for every original edge (u, v),
 * one edge between each token of u and each token of v with weight
 * A_uv / sqrt(k_u k_v). Tokens of vertex v are numbered
 * offset[v] .. offset[v + 1] - 1, in the order of sigma_v; each starts in its
 * own label. With the k's frozen, the disjoint CPM of a token partition
 * equals the unnormalized overlapping potential of the cover it projects to.
 * Normalized values differ, because the token and original total edge
 * weights generally differ; diagnostics record both denominators.
 */

typedef struct {
    igraph_t graph;
    igraph_bool_t has_graph;          /* graph is valid */
    igraph_vector_t edge_weights;
    igraph_vector_t node_weights;
    igraph_vector_int_t membership;   /* token -> label */
    igraph_vector_int_t offset;       /* vertex -> first token; offset[n] = #tokens */
    igraph_int_t token_count;
    igraph_int_t token_edge_count;
} overlap_tokens_t;

static void overlap_tokens_destroy(overlap_tokens_t *tokens) {
    if (tokens->has_graph) {
        igraph_destroy(&tokens->graph);
    }
    igraph_vector_int_destroy(&tokens->offset);
    igraph_vector_int_destroy(&tokens->membership);
    igraph_vector_destroy(&tokens->node_weights);
    igraph_vector_destroy(&tokens->edge_weights);
}

static igraph_error_t overlap_tokens_init(overlap_tokens_t *tokens) {
    IGRAPH_CHECK(igraph_vector_init(&tokens->edge_weights, 0));
    IGRAPH_CHECK(igraph_vector_init(&tokens->node_weights, 0));
    IGRAPH_CHECK(igraph_vector_int_init(&tokens->membership, 0));
    IGRAPH_CHECK(igraph_vector_int_init(&tokens->offset, 0));
    return IGRAPH_SUCCESS;
}

/* Numbers the tokens: offset[v] is the first token of vertex v. */
static igraph_error_t overlap_token_offsets(overlap_tokens_t *tokens,
                                            const igraph_vector_int_list_t *memberships) {
    const igraph_int_t n = igraph_vector_int_list_size(memberships);
    igraph_int_t offset_size, nb_tokens = 0;

    IGRAPH_SAFE_ADD(n, 1, &offset_size);
    IGRAPH_CHECK(igraph_vector_int_resize(&tokens->offset, offset_size));
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_int_t k = igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, v));
        VECTOR(tokens->offset)[v] = nb_tokens;
        IGRAPH_SAFE_ADD(nb_tokens, k, &nb_tokens);
    }
    VECTOR(tokens->offset)[n] = nb_tokens;
    tokens->token_count = nb_tokens;
    return IGRAPH_SUCCESS;
}

/* Token weights n_v / sqrt(k_v); every token starts in its label. */
static igraph_error_t overlap_token_vertices(overlap_tokens_t *tokens,
                                             const igraph_vector_int_list_t *memberships,
                                             const igraph_vector_t *node_weights) {
    const igraph_int_t n = igraph_vector_int_list_size(memberships);

    IGRAPH_CHECK(igraph_vector_resize(&tokens->node_weights, tokens->token_count));
    IGRAPH_CHECK(igraph_vector_int_resize(&tokens->membership, tokens->token_count));
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(sigma);
        const igraph_real_t fv = 1.0 / sqrt((igraph_real_t) k);
        for (igraph_int_t idx = 0; idx < k; idx++) {
            const igraph_int_t t = VECTOR(tokens->offset)[v] + idx;
            VECTOR(tokens->node_weights)[t] = VECTOR(*node_weights)[v] * fv;
            VECTOR(tokens->membership)[t] = VECTOR(*sigma)[idx];
        }
    }
    return IGRAPH_SUCCESS;
}

/* Counts the token edges, sum_(uv in E) k_u k_v, before anything grows, and
 * rejects a token graph beyond igraph's edge-count limit. */
static igraph_error_t overlap_token_edge_count(overlap_tokens_t *tokens, const igraph_t *graph,
                                               const igraph_vector_int_list_t *memberships) {
    const igraph_int_t m = igraph_ecount(graph);
    igraph_int_t nb_token_edges = 0;

    for (igraph_int_t e = 0; e < m; e++) {
        const igraph_int_t from = IGRAPH_FROM(graph, e);
        const igraph_int_t to = IGRAPH_TO(graph, e);
        igraph_int_t pair_edges;
        if (from == to) {
            continue;
        }
        IGRAPH_SAFE_MULT(
            igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, from)),
            igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, to)),
            &pair_edges);
        IGRAPH_SAFE_ADD(nb_token_edges, pair_edges, &nb_token_edges);
        if (nb_token_edges > IGRAPH_ECOUNT_MAX) {
            IGRAPH_ERROR("Overlapping Leiden token graph exceeds igraph's edge-count limit.",
                         IGRAPH_EOVERFLOW);
        }
    }
    tokens->token_edge_count = nb_token_edges;
    return IGRAPH_SUCCESS;
}

/* Emits every token edge into `token_edges` (reserved here) and the token
 * edge weights. */
static igraph_error_t overlap_token_edges(overlap_tokens_t *tokens, const igraph_t *graph,
                                         const igraph_vector_t *edge_weights,
                                         const igraph_vector_int_list_t *memberships,
                                         igraph_vector_int_t *token_edges) {
    const igraph_int_t m = igraph_ecount(graph);
    igraph_int_t token_endpoint_count;
    int interruption_counter = 0;

    IGRAPH_SAFE_MULT(tokens->token_edge_count, 2, &token_endpoint_count);
    IGRAPH_CHECK(igraph_vector_int_reserve(token_edges, token_endpoint_count));
    IGRAPH_CHECK(igraph_vector_reserve(&tokens->edge_weights, tokens->token_edge_count));

    for (igraph_int_t e = 0; e < m; e++) {
        const igraph_int_t from = IGRAPH_FROM(graph, e), to = IGRAPH_TO(graph, e);
        igraph_int_t kf, kt;
        igraph_real_t wff;
        if (from == to) {
            continue;
        }
        kf = igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, from));
        kt = igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, to));
        wff = VECTOR(*edge_weights)[e] / (sqrt((igraph_real_t) kf) * sqrt((igraph_real_t) kt));
        for (igraph_int_t i = 0; i < kf; i++) {
            for (igraph_int_t j = 0; j < kt; j++) {
                IGRAPH_CHECK(igraph_vector_int_push_back(token_edges, VECTOR(tokens->offset)[from] + i));
                IGRAPH_CHECK(igraph_vector_int_push_back(token_edges, VECTOR(tokens->offset)[to] + j));
                IGRAPH_CHECK(igraph_vector_push_back(&tokens->edge_weights, wff));
                IGRAPH_CHECK(leiden_check_interruption(&interruption_counter, 1 << 13));
            }
        }
    }
    return IGRAPH_SUCCESS;
}

/* Builds the token graph of the cover (the self-loop skips are defensive;
 * the overlapping entry points reject looped input). */
static igraph_error_t overlap_build_tokens(overlap_tokens_t *tokens, const overlap_run_t *run) {
    igraph_vector_int_t token_edges;

    IGRAPH_CHECK(overlap_token_offsets(tokens, run->memberships));
    IGRAPH_CHECK(overlap_token_vertices(tokens, run->memberships, run->node_weights));
    IGRAPH_VECTOR_INT_INIT_FINALLY(&token_edges, 0);
    igraph_vector_clear(&tokens->edge_weights);
    IGRAPH_CHECK(overlap_token_edge_count(tokens, run->graph, run->memberships));
    IGRAPH_CHECK(overlap_token_edges(tokens, run->graph, run->edge_weights, run->memberships,
                                     &token_edges));
    IGRAPH_CHECK(igraph_create(&tokens->graph, &token_edges, tokens->token_count,
                               IGRAPH_UNDIRECTED));
    tokens->has_graph = true;
    igraph_vector_int_destroy(&token_edges);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* Projects the token clustering back to label rows. Two tokens of one vertex
 * that ended in the same label collapse (multiset -> set); *deduped reports
 * whether that happened and *collision_count (if given) how often. */
static igraph_error_t overlap_project_tokens(const overlap_tokens_t *tokens,
                                             igraph_vector_int_list_t *memberships,
                                             igraph_bool_t *deduped,
                                             igraph_int_t *collision_count) {
    const igraph_int_t n = igraph_vector_int_list_size(memberships);
    igraph_vector_int_t labels;

    IGRAPH_VECTOR_INT_INIT_FINALLY(&labels, 0);
    *deduped = false;
    if (collision_count) {
        *collision_count = 0;
    }
    for (igraph_int_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t start = VECTOR(tokens->offset)[v];
        const igraph_int_t kt = VECTOR(tokens->offset)[v + 1] - start;
        igraph_int_t distinct = 0;

        IGRAPH_CHECK(igraph_vector_int_resize(&labels, kt));
        for (igraph_int_t idx = 0; idx < kt; idx++) {
            VECTOR(labels)[idx] = VECTOR(tokens->membership)[start + idx];
        }
        igraph_vector_int_sort(&labels);

        IGRAPH_CHECK(igraph_vector_int_resize(sigma, kt));
        for (igraph_int_t idx = 0; idx < kt; idx++) {
            if (idx == 0 || VECTOR(labels)[idx] != VECTOR(labels)[idx - 1]) {
                VECTOR(*sigma)[distinct] = VECTOR(labels)[idx];
                distinct++;
            }
        }
        if (distinct < kt) {
            *deduped = true;
            if (collision_count) {
                *collision_count += kt - distinct;
            }
            IGRAPH_CHECK(igraph_vector_int_resize(sigma, distinct));
        }
    }
    igraph_vector_int_destroy(&labels);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 4.6  One multilevel iteration
 * -----------------------------------------------------------------------------
 *
 *   (1) overlapping local moving on the original graph (Section 4.4);
 *   (2) freeze the row sizes and build the token graph (Section 4.5);
 *   (3) run the complete disjoint multilevel machinery on the tokens
 *       (Section 3.6, tolerant mode, isolation always allowed so it can seed
 *       new token clusters);
 *   (4) project back to rows, collapsing duplicates.
 *
 * With local_move_only, only step (1) runs. Otherwise the cover reached by
 * step (1) is saved, with its quality, for the guard of Section 4.7.
 */

/* Resets a checkpoint: counts and flags to zero, measurements to NaN. */
static void overlap_checkpoint_reset(overlap_checkpoint_t *checkpoint) {
    *checkpoint = (overlap_checkpoint_t) {
        .token_weight = IGRAPH_NAN,
        .quality_after_local = IGRAPH_NAN,
        .original_unnormalized = IGRAPH_NAN,
        .token_initial_quality = IGRAPH_NAN,
        .token_initial_unnormalized = IGRAPH_NAN,
        .token_identity_abs_error = IGRAPH_NAN,
        .token_final_quality = IGRAPH_NAN,
        .quality_projected = IGRAPH_NAN
    };
}

/* Step (1), followed by compaction of the labels. */
static igraph_error_t overlap_local_phase(const overlap_run_t *run, igraph_bool_t *phase_changed,
                                          igraph_int_t *nb_comms) {
    igraph_inclist_t edges_per_node;

    IGRAPH_CHECK(igraph_inclist_init(run->graph, &edges_per_node, IGRAPH_ALL, IGRAPH_LOOPS_TWICE));
    IGRAPH_FINALLY(igraph_inclist_destroy, &edges_per_node);
    IGRAPH_CHECK(overlap_fastmove_nodes(run, &edges_per_node, phase_changed));
    igraph_inclist_destroy(&edges_per_node);
    IGRAPH_FINALLY_CLEAN(1);
    return overlap_compact(run->memberships, nb_comms);
}

/* The cover after local moving and its quality, kept for the guard. */
typedef struct {
    igraph_vector_int_list_t *cover;   /* copy of the rows */
    igraph_real_t quality;
    igraph_real_t magnitude;           /* rounding bound inputs (Section 4.3) */
    igraph_int_t terms;
} overlap_local_state_t;

static igraph_error_t overlap_save_local_state(const overlap_run_t *run,
                                               overlap_local_state_t *local) {
    IGRAPH_CHECK(overlap_copy_cover(local->cover, run->memberships));
    return overlap_quality_ext(run->graph, run->edge_weights, run->node_weights,
                               run->memberships, run->resolution, &local->quality,
                               &local->magnitude, &local->terms);
}

/* Diagnostics: checks that the token graph reproduces the unnormalized
 * potential of the cover it was built from. Both sides are recomputed sums
 * of the same terms, split differently, so the bound adds their
 * recursive-summation error to the tie margin. */
static igraph_error_t overlap_check_token_identity(const overlap_run_t *run,
                                                   const overlap_tokens_t *tokens,
                                                   const overlap_local_state_t *local,
                                                   igraph_int_t nb_comms,
                                                   overlap_checkpoint_t *checkpoint) {
    igraph_real_t identity_tolerance;

    IGRAPH_CHECK(leiden_quality(&tokens->graph, &tokens->edge_weights, &tokens->node_weights,
                                NULL, &tokens->membership, nb_comms, run->resolution,
                                &checkpoint->token_initial_quality));
    checkpoint->token_initial_unnormalized =
        checkpoint->token_initial_quality * checkpoint->token_weight;
    identity_tolerance = leiden_tolerance(checkpoint->original_unnormalized,
                                          checkpoint->token_initial_unnormalized) +
        DBL_EPSILON * local->magnitude *
        (igraph_real_t) (local->terms + checkpoint->token_edge_count + nb_comms + 2);
    checkpoint->token_identity_abs_error =
        fabs(checkpoint->original_unnormalized - checkpoint->token_initial_unnormalized);
    if (checkpoint->token_identity_abs_error > identity_tolerance) {
        IGRAPH_ERRORF("Overlapping Leiden token identity mismatch "
                      "(original=%g, token=%g, tolerance=%g).",
                      IGRAPH_EINTERNAL, checkpoint->original_unnormalized,
                      checkpoint->token_initial_unnormalized, identity_tolerance);
    }
    return IGRAPH_SUCCESS;
}

/* Steps (2)-(4). Sets *token_changed if the token stage moved anything and
 * *dedup_changed if projection collapsed duplicates. */
static igraph_error_t overlap_token_phase(const overlap_run_t *run,
                                          const overlap_local_state_t *local,
                                          igraph_int_t nb_comms,
                                          overlap_checkpoint_t *checkpoint,
                                          igraph_bool_t *token_changed,
                                          igraph_bool_t *dedup_changed) {
    const leiden_options_t token_options = {
        .resolution = run->resolution,
        .beta = run->beta,
        .allow_isolation = true,
        .local_move_only = false,
        .max_total_communities = run->max_total_communities,
        .n_communities = run->n_communities,
        .tolerant = true
    };
    overlap_tokens_t tokens = { .has_graph = false };
    igraph_int_t token_nb_clusters;

    IGRAPH_FINALLY(overlap_tokens_destroy, &tokens);
    IGRAPH_CHECK(overlap_tokens_init(&tokens));
    IGRAPH_CHECK(overlap_build_tokens(&tokens, run));
    if (checkpoint) {
        checkpoint->token_count = tokens.token_count;
        checkpoint->token_edge_count = tokens.token_edge_count;
        checkpoint->token_weight = igraph_vector_sum(&tokens.edge_weights);
        IGRAPH_CHECK(overlap_check_token_identity(run, &tokens, local, nb_comms, checkpoint));
    }

    IGRAPH_CHECK(community_leiden(&tokens.graph, &tokens.edge_weights, &tokens.node_weights, NULL,
                                  &token_options, &tokens.membership, &token_nb_clusters,
                                  checkpoint ? &checkpoint->token_final_quality : NULL,
                                  token_changed));
    IGRAPH_CHECK(overlap_project_tokens(&tokens, run->memberships, dedup_changed,
                                        checkpoint ? &checkpoint->collision_count : NULL));

    overlap_tokens_destroy(&tokens);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* One iteration (steps (1)-(4)). In full mode `local` receives the cover
 * reached by step (1); `checkpoint` (diagnostics only) receives the
 * measurements of the iteration. Sets *changed if anything changed. */
static igraph_error_t overlap_iteration(const overlap_run_t *run,
                                        overlap_local_state_t *local,
                                        overlap_checkpoint_t *checkpoint,
                                        igraph_bool_t *changed) {
    igraph_bool_t phase_changed = false, token_changed = false, dedup_changed = false;
    igraph_int_t nb_comms;

    if (checkpoint) {
        overlap_checkpoint_reset(checkpoint);
    }
    IGRAPH_CHECK(overlap_local_phase(run, &phase_changed, &nb_comms));
    if (run->local_move_only) {
        *changed = phase_changed;
        return IGRAPH_SUCCESS;
    }

    IGRAPH_CHECK(overlap_save_local_state(run, local));
    if (checkpoint) {
        checkpoint->original_weight = igraph_vector_sum(run->edge_weights);
        checkpoint->local_changed = phase_changed;
        checkpoint->quality_after_local = local->quality;
        checkpoint->original_unnormalized =
            checkpoint->quality_after_local * checkpoint->original_weight;
    }
        IGRAPH_CHECK(overlap_count_labels(local->cover, &checkpoint->labels_local));

    IGRAPH_CHECK(overlap_token_phase(run, local, nb_comms, checkpoint, &token_changed,
                                     &dedup_changed));
    if (checkpoint) {
        checkpoint->token_changed = token_changed;
        checkpoint->dedup_changed = dedup_changed;
        IGRAPH_CHECK(overlap_quality(run->graph, run->edge_weights, run->node_weights,
                                     run->memberships, run->resolution,
                                     &checkpoint->quality_projected));
        IGRAPH_CHECK(overlap_count_labels(run->memberships, &checkpoint->labels_proposed));
    }
    if (phase_changed || token_changed || dedup_changed) {
        *changed = true;
    }
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 4.7  Original-space guard and certificate sweeps
 * -----------------------------------------------------------------------------
 *
 * After every full-mode iteration the projected proposal is compared, in the
 * original graph, with the cover reached by that iteration's local moving:
 *
 *   - it is kept if its quality is higher beyond the tie margin;
 *   - it is also kept if it is within the margin (not worse beyond it) and
 *     occupies strictly fewer labels: projection merges labels with
 *     identical members, which single-vertex moves cannot merge; at most n
 *     such ties are kept per call, so the iterations terminate;
 *   - otherwise the local-moving cover is restored (so the local improvement
 *     is never lost) and the iterations end.
 *
 * When the caller asked for convergence (n_iterations < 0), the run finishes
 * with local-moving sweeps until one moves nothing: token refinement,
 * aggregation and rollback can leave a cover that is not an overlapping best
 * response. This is the Nash certificate (Definition 3 / Proposition 1 of
 * Felipe, Avrachenkov & Menasche, 2025), up to the tie margin. In
 * local-moving-only mode the last iteration already was such a sweep.
 */

typedef struct {
    igraph_vector_int_list_t local_cover;   /* rows after the iteration's local moving */
    igraph_real_t committed_quality;        /* quality of the cover kept so far */
    igraph_int_t tie_budget;                /* tied proposals that may still be kept */
} overlap_guard_t;

static void overlap_guard_destroy(overlap_guard_t *guard) {
    igraph_vector_int_list_destroy(&guard->local_cover);
}

static igraph_error_t overlap_guard_init(overlap_guard_t *guard, const overlap_run_t *run) {
    const igraph_int_t n = igraph_vcount(run->graph);

    guard->tie_budget = n;
    IGRAPH_CHECK(igraph_vector_int_list_init(&guard->local_cover, n));
    return overlap_quality(run->graph, run->edge_weights, run->node_weights, run->memberships,
                           run->resolution, &guard->committed_quality);
}

/* Decides whether to keep the proposal (quality q_cur) over the local-moving
 * cover (quality q_local), spending one tie if a tie is kept. */
static igraph_error_t overlap_guard_keeps(const overlap_run_t *run, overlap_guard_t *guard,
                                          igraph_real_t q_cur, igraph_real_t q_local,
                                          igraph_bool_t *keep) {
    *keep = leiden_is_improvement(q_cur, q_local);
    if (!*keep && guard->tie_budget > 0 && !leiden_is_improvement(q_local, q_cur)) {
        igraph_int_t labels_proposed, labels_local;
        IGRAPH_CHECK(overlap_count_labels(run->memberships, &labels_proposed));
        IGRAPH_CHECK(overlap_count_labels(&guard->local_cover, &labels_local));
        *keep = labels_proposed < labels_local;
        guard->tie_budget -= *keep;
    }
    return IGRAPH_SUCCESS;
}

/* Diagnostics: appends one row to the projection trace. */
static igraph_error_t overlap_record_projection(const overlap_run_t *run, igraph_int_t itr,
                                                const overlap_checkpoint_t *checkpoint,
                                                igraph_real_t quality_before,
                                                igraph_bool_t accepted,
                                                igraph_real_t committed_quality) {
    igraph_real_t values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TRACE_WIDTH];

    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_ITERATION] = itr;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_ORIGINAL_WEIGHT] = checkpoint->original_weight;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_WEIGHT] = checkpoint->token_weight;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_QUALITY_BEFORE] = quality_before;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_QUALITY_AFTER_LOCAL] = checkpoint->quality_after_local;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_ORIGINAL_UNNORMALIZED] = checkpoint->original_unnormalized;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_INITIAL_QUALITY] = checkpoint->token_initial_quality;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_INITIAL_UNNORMALIZED] =
        checkpoint->token_initial_unnormalized;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_IDENTITY_ABS_ERROR] =
        checkpoint->token_identity_abs_error;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_FINAL_QUALITY] = checkpoint->token_final_quality;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_COUNT] = checkpoint->token_count;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_EDGE_COUNT] = checkpoint->token_edge_count;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_COLLISION_COUNT] = checkpoint->collision_count;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_QUALITY_PROJECTED] = checkpoint->quality_projected;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_ACCEPTED] = accepted;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_QUALITY_COMMITTED] = committed_quality;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_LOCAL_CHANGED] = checkpoint->local_changed;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_TOKEN_CHANGED] = checkpoint->token_changed;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_DEDUP_CHANGED] = checkpoint->dedup_changed;
    return overlap_trace_append(run->projection_trace, values,
                                IGRAPH_LEIDEN_OVERLAP_PROJECTION_TRACE_WIDTH);
}

/* One full-mode iteration followed by the guard. Sets *stop when the
 * proposal was rejected (the local cover is then restored). */
static igraph_error_t overlap_guarded_iteration(const overlap_run_t *run, overlap_guard_t *guard,
                                                igraph_int_t itr, igraph_bool_t *changed,
                                                igraph_bool_t *stop) {
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_LABELS_LOCAL] = checkpoint->labels_local;
    values[IGRAPH_LEIDEN_OVERLAP_PROJECTION_LABELS_PROPOSED] = checkpoint->labels_proposed;
    const igraph_real_t quality_before = guard->committed_quality;
    overlap_local_state_t local = { .cover = &guard->local_cover, .quality = IGRAPH_NAN };
    overlap_checkpoint_t checkpoint;
    overlap_checkpoint_t *checkpoint_ptr = run->projection_trace ? &checkpoint : NULL;
    igraph_real_t q_cur;
    igraph_bool_t keep;

    IGRAPH_CHECK(overlap_iteration(run, &local, checkpoint_ptr, changed));
    if (checkpoint_ptr) {
        q_cur = checkpoint.quality_projected;
    } else {
        IGRAPH_CHECK(overlap_quality(run->graph, run->edge_weights, run->node_weights,
                                     run->memberships, run->resolution, &q_cur));
    }
    IGRAPH_CHECK(overlap_guard_keeps(run, guard, q_cur, local.quality, &keep));
    if (keep) {
        guard->committed_quality = q_cur;
    } else {
        IGRAPH_CHECK(overlap_copy_cover(run->memberships, &guard->local_cover));
        *changed = false;
        guard->committed_quality = local.quality;
    }
    if (checkpoint_ptr) {
        IGRAPH_CHECK(overlap_record_projection(run, itr, &checkpoint, quality_before, keep,
                                               guard->committed_quality));
    }
    *stop = !keep;
    return IGRAPH_SUCCESS;
}

/* Runs n_iterations iterations (until nothing changes if negative), with the
 * guard in full mode. */
static igraph_error_t overlap_iterate(const overlap_run_t *run, igraph_int_t n_iterations) {
    overlap_guard_t guard = { .tie_budget = 0 };
    igraph_bool_t changed = true, stop = false;

    IGRAPH_FINALLY(overlap_guard_destroy, &guard);
    if (!run->local_move_only) {
        IGRAPH_CHECK(overlap_guard_init(&guard, run));
    }
    for (igraph_int_t itr = 0; n_iterations < 0 ? changed : itr < n_iterations; itr++) {
        if (run->trace) {
            run->trace->stage = itr;
        }
        changed = false;
        if (run->local_move_only) {
            IGRAPH_CHECK(overlap_iteration(run, NULL, NULL, &changed));
            continue;
        }
        IGRAPH_CHECK(overlap_guarded_iteration(run, &guard, itr, &changed, &stop));
        if (stop) {
            break;
        }
    }
    overlap_guard_destroy(&guard);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* Local-moving sweeps until one moves nothing (full mode, n_iterations < 0).
 * Diagnostic stages -1, -2, ... identify the sweeps. */
static igraph_error_t overlap_certificate_sweeps(const overlap_run_t *run) {
    igraph_inclist_t edges_per_node;
    igraph_int_t certificate_sweep = 0;
    igraph_bool_t changed;

    IGRAPH_CHECK(igraph_inclist_init(run->graph, &edges_per_node, IGRAPH_ALL, IGRAPH_LOOPS_TWICE));
    IGRAPH_FINALLY(igraph_inclist_destroy, &edges_per_node);
    do {
        changed = false;
        if (run->trace) {
            run->trace->stage = -(certificate_sweep + 1);
        }
        IGRAPH_CHECK(overlap_fastmove_nodes(run, &edges_per_node, &changed));
        certificate_sweep++;
    } while (changed);
    igraph_inclist_destroy(&edges_per_node);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 4.8  Input validation and start covers
 * -----------------------------------------------------------------------------
 *
 * The overlapping path accepts undirected, loopless graphs with at least one
 * edge, finite non-negative edge weights with a positive total, finite
 * non-negative node weights, a finite resolution and 0 <= beta < infinity;
 * max_memberships <= n. Magnitude checks reject inputs whose objective
 * arithmetic could overflow. The disjoint path keeps its historical contract.
 */

/* Graph shape and scalar parameters. */
static igraph_error_t overlap_validate_graph_and_parameters(const igraph_t *graph,
                                                            igraph_real_t resolution,
                                                            igraph_real_t beta,
                                                            igraph_int_t max_memberships) {
    const igraph_int_t n = igraph_vcount(graph);
    const igraph_int_t m = igraph_ecount(graph);
    igraph_int_t label_bound, label_storage_bound;
    igraph_bool_t has_loop;

    if (igraph_is_directed(graph)) {
        IGRAPH_ERROR("Overlapping Leiden requires an undirected graph.", IGRAPH_EINVAL);
    }
    IGRAPH_CHECK(igraph_has_loop(graph, &has_loop));
    if (has_loop) {
        IGRAPH_ERROR("Overlapping Leiden requires a loopless graph.", IGRAPH_EINVAL);
    }
    if (n < 1 || m < 1) {
        IGRAPH_ERROR("Overlapping Leiden requires a nonempty graph with at least one edge.",
                     IGRAPH_EINVAL);
    }
    if (!isfinite(resolution)) {
        IGRAPH_ERROR("Overlapping Leiden resolution must be finite.", IGRAPH_EINVAL);
    }
    if (!isfinite(beta) || beta < 0.0) {
        IGRAPH_ERROR("Overlapping Leiden beta must be finite and non-negative.", IGRAPH_EINVAL);
    }
    if (max_memberships > n) {
        IGRAPH_ERROR("Overlapping Leiden max_memberships must not exceed the number of vertices.",
                     IGRAPH_EINVAL);
    }
    /* The anonymous label bank n * M (+1) must be representable. */
    IGRAPH_SAFE_MULT(n, max_memberships, &label_bound);
    IGRAPH_SAFE_ADD(label_bound, 1, &label_storage_bound);
    (void) label_storage_bound;
    return IGRAPH_SUCCESS;
}

/* Edge weights: length, sign, finiteness, and a total that is positive and
 * small enough for the potential arithmetic. */
static igraph_error_t overlap_validate_edge_weights(const igraph_t *graph,
                                                    const igraph_vector_t *edge_weights,
                                                    igraph_int_t max_memberships) {
    const igraph_int_t m = igraph_ecount(graph);
    igraph_real_t total_edge_weight = edge_weights ? 0.0 : (igraph_real_t) m;
    igraph_real_t safe_total_edge_weight;

    if (edge_weights) {
        if (igraph_vector_size(edge_weights) != m) {
            IGRAPH_ERROR("Edge weight vector length does not match the number of edges.",
                         IGRAPH_EINVAL);
        }
        if (!igraph_vector_is_all_finite(edge_weights) || igraph_vector_min(edge_weights) < 0.0) {
            IGRAPH_ERROR("Overlapping Leiden edge weights must be finite and non-negative.",
                         IGRAPH_EINVAL);
        }
        for (igraph_int_t e = 0; e < m; e++) {
            total_edge_weight += VECTOR(*edge_weights)[e];
            if (!isfinite(total_edge_weight)) {
                IGRAPH_ERROR("Overlapping Leiden total edge weight overflowed.", IGRAPH_EOVERFLOW);
            }
        }
    }
    if (!(total_edge_weight > 0.0) || !isfinite(total_edge_weight)) {
        IGRAPH_ERROR("Overlapping Leiden requires positive finite total edge weight.",
                     IGRAPH_EINVAL);
    }
    safe_total_edge_weight = DBL_MAX / 4.0 / (igraph_real_t) max_memberships;
    if (total_edge_weight > safe_total_edge_weight) {
        IGRAPH_ERROR("Overlapping Leiden edge-weight arithmetic would overflow.", IGRAPH_EOVERFLOW);
    }
    return IGRAPH_SUCCESS;
}

/* Node weights: length, sign and finiteness. Returns their total (n if
 * NULL). */
static igraph_error_t overlap_validate_node_weights(const igraph_t *graph,
                                                    const igraph_vector_t *node_weights,
                                                    igraph_real_t *total_node_weight) {
    const igraph_int_t n = igraph_vcount(graph);

    *total_node_weight = node_weights ? 0.0 : (igraph_real_t) n;
    if (!node_weights) {
        return IGRAPH_SUCCESS;
    }
    if (igraph_vector_size(node_weights) != n) {
        IGRAPH_ERROR("Node weight vector length does not match the number of vertices.",
                     IGRAPH_EINVAL);
    }
    if (!igraph_vector_is_all_finite(node_weights) || igraph_vector_min(node_weights) < 0.0) {
        IGRAPH_ERROR("Overlapping Leiden node weights must be finite and non-negative.",
                     IGRAPH_EINVAL);
    }
    for (igraph_int_t v = 0; v < n; v++) {
        *total_node_weight += VECTOR(*node_weights)[v];
        if (!isfinite(*total_node_weight)) {
            IGRAPH_ERROR("Overlapping Leiden total node weight overflowed.", IGRAPH_EOVERFLOW);
        }
    }
    return IGRAPH_SUCCESS;
}

/* The largest mass penalty is |gamma| (sum_v n_v)^2; token collisions can
 * concentrate at most another factor M in one temporary token label. */
static igraph_error_t overlap_validate_crowding(igraph_real_t resolution,
                                                igraph_real_t total_node_weight,
                                                igraph_int_t max_memberships) {
    if (total_node_weight > 1.0 && resolution != 0.0) {
        igraph_real_t safe_resolution = DBL_MAX / 2.0 / (igraph_real_t) max_memberships;
        safe_resolution /= total_node_weight;
        safe_resolution /= total_node_weight;
        if (fabs(resolution) > safe_resolution) {
            IGRAPH_ERROR("Overlapping Leiden crowding term would overflow.", IGRAPH_EOVERFLOW);
        }
    }
    return IGRAPH_SUCCESS;
}

/* Multilevel mode builds up to m * M^2 token edges. */
static igraph_error_t overlap_validate_token_bound(const igraph_t *graph,
                                                   igraph_int_t max_memberships,
                                                   igraph_bool_t local_move_only) {
    igraph_int_t cap_squared, token_edge_bound;

    if (local_move_only) {
        return IGRAPH_SUCCESS;
    }
    IGRAPH_SAFE_MULT(max_memberships, max_memberships, &cap_squared);
    IGRAPH_SAFE_MULT(igraph_ecount(graph), cap_squared, &token_edge_bound);
    if (token_edge_bound > IGRAPH_ECOUNT_MAX) {
        IGRAPH_ERROR("Overlapping Leiden token graph may exceed igraph's edge-count limit.",
                     IGRAPH_EOVERFLOW);
    }
    return IGRAPH_SUCCESS;
}

/* The complete domain check, before any workspace is allocated. */
static igraph_error_t overlap_validate_domain(const igraph_t *graph,
                                              const igraph_vector_t *edge_weights,
                                              const igraph_vector_t *node_weights,
                                              igraph_real_t resolution,
                                              igraph_real_t beta,
                                              igraph_int_t max_memberships,
                                              igraph_bool_t local_move_only) {
    igraph_real_t total_node_weight;

    IGRAPH_CHECK(overlap_validate_graph_and_parameters(graph, resolution, beta, max_memberships));
    IGRAPH_CHECK(overlap_validate_edge_weights(graph, edge_weights, max_memberships));
    IGRAPH_CHECK(overlap_validate_node_weights(graph, node_weights, &total_node_weight));
    IGRAPH_CHECK(overlap_validate_crowding(resolution, total_node_weight, max_memberships));
    IGRAPH_CHECK(overlap_validate_token_bound(graph, max_memberships, local_move_only));
    return IGRAPH_SUCCESS;
}

/* Sorts a row and removes duplicate labels. */
static igraph_error_t overlap_sort_unique_row(igraph_vector_int_t *sigma) {
    const igraph_int_t k = igraph_vector_int_size(sigma);
    igraph_int_t distinct = 1;

    igraph_vector_int_sort(sigma);
    for (igraph_int_t idx = 1; idx < k; idx++) {
        if (VECTOR(*sigma)[idx] != VECTOR(*sigma)[distinct - 1]) {
            VECTOR(*sigma)[distinct] = VECTOR(*sigma)[idx];
            distinct++;
        }
    }
    if (distinct < k) {
        IGRAPH_CHECK(igraph_vector_int_resize(sigma, distinct));
    }
    return IGRAPH_SUCCESS;
}

/* Validates a supplied start cover and normalizes it in place: every row
 * non-empty, sorted and duplicate-free, at most M labels, labels in
 * [0, n * M). Labels are compacted separately. */
static igraph_error_t overlap_validate_start(igraph_int_t n, igraph_int_t max_memberships,
                                             igraph_vector_int_list_t *memberships) {
    igraph_int_t label_bound;

    IGRAPH_SAFE_MULT(n, max_memberships, &label_bound);
    for (igraph_int_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_int_t k;

        if (igraph_vector_int_size(sigma) < 1) {
            IGRAPH_ERROR("Initial overlapping membership vectors must be non-empty.",
                         IGRAPH_EINVAL);
        }
        IGRAPH_CHECK(overlap_sort_unique_row(sigma));
        k = igraph_vector_int_size(sigma);
        if (k > max_memberships) {
            IGRAPH_ERROR("Initial overlapping membership vector exceeds max_memberships.",
                         IGRAPH_EINVAL);
        }
        if (VECTOR(*sigma)[0] < 0 || VECTOR(*sigma)[k - 1] >= label_bound) {
            IGRAPH_ERROR("Initial overlapping membership indices must be non-negative "
                         "and less than n * max_memberships.", IGRAPH_EINVAL);
        }
    }
    return IGRAPH_SUCCESS;
}

/* The start cover without a supplied one: singletons, or a deterministic
 * feasible cover for a count limit. With a target K <= n, vertex v starts in
 * label v mod K; an exact K > n adds labels n .. K - 1 round-robin to the
 * singleton rows (the caller has checked K <= n * M). */
static igraph_error_t overlap_default_start(igraph_int_t n, igraph_int_t max_total_communities,
                                            igraph_int_t n_communities,
                                            igraph_vector_int_list_t *memberships,
                                            igraph_int_t *nb_clusters) {
    const igraph_int_t target = n_communities > 0 ? n_communities :
        (max_total_communities > 0 && max_total_communities < n) ? max_total_communities : n;

    IGRAPH_CHECK(igraph_vector_int_list_resize(memberships, n));
    for (igraph_int_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        IGRAPH_CHECK(igraph_vector_int_resize(sigma, 1));
        VECTOR(*sigma)[0] = target < n ? v % target : v;
    }
    for (igraph_int_t c = n; c < target; c++) {
        IGRAPH_CHECK(igraph_vector_int_push_back(
            igraph_vector_int_list_get_ptr(memberships, (c - n) % n), c));
    }
    if (target != n) {
        IGRAPH_CHECK(overlap_compact(memberships, nb_clusters));
    }
    return IGRAPH_SUCCESS;
}

/* A start cover that violates a count limit is rejected, not repaired. */
static igraph_error_t overlap_check_start_counts(igraph_vector_int_list_t *memberships,
                                                 igraph_int_t max_total_communities,
                                                 igraph_int_t n_communities) {
    igraph_int_t initial_labels;

    if (max_total_communities <= 0 && n_communities <= 0) {
        return IGRAPH_SUCCESS;
    }
    IGRAPH_CHECK(overlap_compact(memberships, &initial_labels));
    if (max_total_communities > 0 && initial_labels > max_total_communities) {
        IGRAPH_ERROR("Initial cover exceeds max_total_communities.", IGRAPH_EINVAL);
    }
    if (n_communities > 0 && initial_labels != n_communities) {
        IGRAPH_ERROR("Initial cover does not contain exactly n_communities labels.",
                     IGRAPH_EINVAL);
    }
    return IGRAPH_SUCCESS;
}

/* Prepares the start cover: the supplied one (validated, normalized and
 * compacted) or the default one, and checks it against the count limits. */
static igraph_error_t overlap_prepare_start(igraph_int_t n, igraph_int_t max_memberships,
                                            igraph_int_t max_total_communities,
                                            igraph_int_t n_communities, igraph_bool_t start,
                                            igraph_vector_int_list_t *memberships,
                                            igraph_int_t *nb_clusters) {
    if (start) {
        IGRAPH_CHECK(overlap_validate_start(n, max_memberships, memberships));
        IGRAPH_CHECK(overlap_compact(memberships, nb_clusters));
    } else {
        IGRAPH_CHECK(overlap_default_start(n, max_total_communities, n_communities, memberships,
                                           nb_clusters));
    }
    return overlap_check_start_counts(memberships, max_total_communities, n_communities);
}

/* Checks the request before any allocation: the output list, the domain,
 * the start length, and that an exact count fits into n * M labels. */
static igraph_error_t overlap_check_request(const igraph_t *graph,
                                            const igraph_vector_t *edge_weights,
                                            const igraph_vector_t *node_weights,
                                            igraph_real_t resolution, igraph_real_t beta,
                                            igraph_int_t max_memberships,
                                            igraph_int_t n_communities, igraph_bool_t start,
                                            igraph_bool_t local_move_only,
                                            const igraph_vector_int_list_t *memberships) {
    const igraph_int_t n = igraph_vcount(graph);

    if (!memberships) {
        IGRAPH_ERROR("Membership list must be provided for overlapping Leiden.", IGRAPH_EINVAL);
    }
    IGRAPH_CHECK(overlap_validate_domain(graph, edge_weights, node_weights, resolution, beta,
                                         max_memberships, local_move_only));
    if (start && igraph_vector_int_list_size(memberships) != n) {
        IGRAPH_ERROR("Initial membership list length does not equal the number of vertices.",
                     IGRAPH_EINVAL);
    }
    if (n_communities > 0) {
        igraph_int_t incidence_bound;
        IGRAPH_SAFE_MULT(n, max_memberships, &incidence_bound);
        if (n_communities > incidence_bound) {
            IGRAPH_ERROR("n_communities exceeds n * max_memberships, the largest number of "
                         "communities a cover can occupy.", IGRAPH_EINVAL);
        }
    }
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 4.9  Overlapping driver
 * -----------------------------------------------------------------------------
 *
 * validate -> resolve weights -> start cover -> guarded iterations ->
 * certificate sweeps -> compact, check counts, quality.
 */

typedef struct {
    leiden_weights_t edge_weights;
    leiden_weights_t node_weights;
} overlap_weights_t;

static void overlap_weights_destroy(overlap_weights_t *weights) {
    leiden_weights_destroy(&weights->node_weights);
    leiden_weights_destroy(&weights->edge_weights);
}

/* Compacts the result, checks the count limits and computes the quality. */
static igraph_error_t overlap_finish(const overlap_run_t *run, igraph_int_t *nb_clusters,
                                     igraph_real_t *quality) {
    IGRAPH_CHECK(overlap_compact(run->memberships, nb_clusters));
    if ((run->max_total_communities > 0 && *nb_clusters > run->max_total_communities) ||
        (run->n_communities > 0 && *nb_clusters != run->n_communities)) {
        IGRAPH_ERROR("Overlapping Leiden returned a cover that violates a community-count "
                     "constraint.", IGRAPH_EINTERNAL);
    }
    if (quality) {
        IGRAPH_CHECK(overlap_quality(run->graph, run->edge_weights, run->node_weights,
                                     run->memberships, run->resolution, quality));
    }
    return IGRAPH_SUCCESS;
}

/* Fills the run description from the resolved weights and, for the
 * diagnostic entry point, points it at a trace record. */
static void overlap_run_describe(overlap_run_t *run, overlap_trace_t *trace,
                                 const igraph_t *graph, const overlap_weights_t *weights,
                                 igraph_real_t resolution, igraph_real_t beta,
                                 igraph_int_t max_memberships,
                                 igraph_int_t max_total_communities,
                                 igraph_int_t n_communities,
                                 igraph_bool_t allow_isolation, igraph_bool_t local_move_only,
                                 igraph_vector_int_list_t *memberships,
                                 igraph_matrix_t *move_trace,
                                 igraph_matrix_t *projection_trace) {
    *run = (overlap_run_t) {
        .graph = graph,
        .edge_weights = weights->edge_weights.vector,
        .node_weights = weights->node_weights.vector,
        .resolution = resolution,
        .beta = beta,
        .max_memberships = max_memberships,
        .max_total_communities = max_total_communities,
        .n_communities = n_communities,
        .allow_isolation = allow_isolation,
        .local_move_only = local_move_only,
        .memberships = memberships,
        .trace = NULL,
        .projection_trace = local_move_only ? NULL : projection_trace
    };
    if (move_trace || projection_trace) {
        *trace = (overlap_trace_t) {
            .move_trace = move_trace,
            .projection_trace = projection_trace,
            .stage = 0,
            .move_sequence = 0,
            .original_weight = igraph_vector_sum(run->edge_weights)
        };
        run->trace = trace;
    }
}

/* The overlapping (max_memberships > 1) path. The trace matrices are NULL
 * except for the diagnostic entry point. */
static igraph_error_t overlap_leiden_run(const igraph_t *graph,
                                         const igraph_vector_t *edge_weights,
                                         const igraph_vector_t *node_weights,
                                         igraph_real_t resolution, igraph_real_t beta,
                                         igraph_int_t max_memberships,
                                         igraph_int_t max_total_communities,
                                         igraph_int_t n_communities,
                                         igraph_bool_t start, igraph_int_t n_iterations,
                                         igraph_bool_t allow_isolation,
                                         igraph_bool_t local_move_only,
                                         igraph_vector_int_list_t *memberships,
                                         igraph_int_t *nb_clusters, igraph_real_t *quality,
                                         igraph_matrix_t *move_trace,
                                         igraph_matrix_t *projection_trace) {
    const igraph_int_t n = igraph_vcount(graph);
    overlap_weights_t weights = { .edge_weights = { .vector = NULL } };
    overlap_trace_t trace;
    overlap_run_t run;
    igraph_int_t i_nb_clusters;

    if (!nb_clusters) {
        nb_clusters = &i_nb_clusters;
    }
    IGRAPH_CHECK(overlap_check_request(graph, edge_weights, node_weights, resolution, beta,
                                       max_memberships, n_communities, start, local_move_only,
                                       memberships));

    IGRAPH_FINALLY(overlap_weights_destroy, &weights);
    IGRAPH_CHECK(leiden_weights_init(&weights.edge_weights, edge_weights, igraph_ecount(graph)));
    IGRAPH_CHECK(leiden_weights_init(&weights.node_weights, node_weights, n));
    overlap_run_describe(&run, &trace, graph, &weights, resolution, beta, max_memberships,
                         max_total_communities, n_communities, allow_isolation, local_move_only,
                         memberships, move_trace, projection_trace);

    IGRAPH_CHECK(overlap_prepare_start(n, max_memberships, max_total_communities, n_communities,
                                       start, memberships, nb_clusters));
    IGRAPH_CHECK(overlap_iterate(&run, n_iterations));
    if (n_iterations < 0 && !local_move_only) {
        IGRAPH_CHECK(overlap_certificate_sweeps(&run));
    }
    IGRAPH_CHECK(overlap_finish(&run, nb_clusters, quality));

    overlap_weights_destroy(&weights);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

/* =============================================================================
 * Section 5  Public API
 * =============================================================================
 *
 * The four entry points. igraph_community_leiden() is the historical
 * interface; igraph_community_leiden_with_constraints() adds global count
 * limits and holds the dispatch to the disjoint (Section 3.7) and
 * overlapping (Section 4.9) paths; the diagnostic entry point records
 * traces; the simple interface derives vertex weights from an objective.
 */

/* -----------------------------------------------------------------------------
 * Section 5.1  igraph_community_leiden
 * -----------------------------------------------------------------------------
 */

/**
 * \ingroup communities
 * \function igraph_community_leiden
 * \brief Finding community structure using the Leiden algorithm.
 *
 * This function implements the Leiden algorithm for finding community
 * structure.
 *
 * </para><para>
 * It is similar to the multilevel algorithm, often called the Louvain
 * algorithm, but it is faster and yields higher quality solutions. It can
 * optimize both modularity and the Constant Potts Model, which does not suffer
 * from the resolution-limit (see Traag, Van Dooren &amp; Nesterov).
 *
 * </para><para>
 * The Leiden algorithm consists of three phases: (1) local moving of vertices, (2)
 * refinement of the partition and (3) aggregation of the network based on the
 * refined partition, using the non-refined partition to create an initial
 * partition for the aggregate network. In the local move procedure in the
 * Leiden algorithm, only vertices whose neighborhood has changed are visited. On
 * the disjoint path, only moves that strictly improve the quality function are
 * made. On the overlapping path, improvements smaller than a scale-aware
 * numerical convergence margin are treated as ties. The refinement is
 * done by restarting from a singleton partition within each cluster and
 * gradually merging the subclusters. When aggregating, a single cluster may
 * then be represented by several vertices (which are the subclusters identified in
 * the refinement).
 *
 * </para><para>
 * The Leiden algorithm provides several guarantees. The Leiden algorithm is
 * typically iterated: the output of one iteration is used as the input for the
 * next iteration. At each iteration all clusters are guaranteed to be (weakly)
 * connected and well-separated. After an iteration in which nothing has
 * changed, all vertices and some parts are guaranteed to be locally optimally
 * assigned. Note that even if a single iteration did not result in any change,
 * it is still possible that a subsequent iteration might find some
 * improvement. Each iteration explores different subsets of vertices to consider
 * for moving from one cluster to another. Finally, asymptotically, all subsets
 * of all clusters are guaranteed to be locally optimally assigned. For more
 * details, please see Traag, Waltman &amp; van Eck (2019).
 *
 * </para><para>
 * The objective function being optimized is
 *
 * </para><para>
 * <code>1 / 2m sum_ij (A_ij - γ n_i n_j) δ(s_i, s_j)</code>
 *
 * </para><para>
 * in the undirected case and
 *
 * </para><para>
 * <code>1 / m sum_ij (A_ij - γ n^out_i n^in_j) δ(s_i, s_j)</code>
 *
 * </para><para>
 * in the directed case.
 * Here \c m is the total edge weight, <code>A_ij</code> is the weight of edge
 * (i, j), \c γ is the so-called resolution parameter, <code>n_i</code>
 * is the vertex weight of vertex \c i (separate out- and in-weights are used
 * with directed graphs), <code>s_i</code> is the cluster of vertex
 * \c i and <code>δ(x, y) = 1</code> if and only if <code>x = y</code> and 0
 * otherwise.
 *
 * </para><para>
 * By setting <code>n_i = k_i</code>, the degree of vertex \c i, and
 * dividing \c γ by <code>2m</code> (by \c m in the directed case), we effectively
 * obtain an expression for modularity. Hence, the standard modularity will be
 * optimized when you supply the degrees (out- and in-degrees with directed graphs)
 * as the vertex weights and by supplying as a resolution parameter
 * <code>1/(2m)</code> (<code>1/m</code> with directed graphs).
 * Use the \ref igraph_community_leiden_simple() convenience function to
 * compute vertex weights automatically for modularity maximization.
 *
 * </para><para>
 * References:
 *
 * </para><para>
 * V. A. Traag, L. Waltman, N. J. van Eck:
 * From Louvain to Leiden: guaranteeing well-connected communities.
 * Scientific Reports, 9(1), 5233 (2019).
 * http://dx.doi.org/10.1038/s41598-019-41695-z
 *
 * </para><para>
 * V. A. Traag, P. Van Dooren, and Y. Nesterov:
 * Narrow scope for resolution-limit-free community detection.
 * Phys. Rev. E 84, 016114 (2011).
 * https://doi.org/10.1103/PhysRevE.84.016114
 *
 * </para><para>
 * L. L. Felipe, K. Avrachenkov, D. S. Menasché:
 * From Leiden to Pleasure Island: The Constant Potts Model for community
 * detection as a hedonic game.
 * Physica A: Statistical Mechanics and its Applications, 680, 130989 (2025).
 * https://doi.org/10.1016/j.physa.2025.130989
 * When \p n_iterations is negative, the implementation finishes with a
 * complete candidate-prefix sweep on the original graph. For overlapping
 * covers this is a floating-point, tolerance-level algorithmic certificate,
 * not an exact-arithmetic proof supplied by the library.
 *
 * \param graph The input graph.
 * \param edge_weights Numeric vector containing edge weights. If \c NULL,
 *    every edge has equal weight of 1. The disjoint path retains its
 *    historical signed-weight contract. The overlapping path requires finite,
 *    non-negative weights with positive finite total weight.
 * \param vertex_out_weights Numeric vector containing vertex weights, or vertex
 *    out-weights for directed graphs. If \c NULL, every vertex has equal
 *    weight of 1. Overlapping node weights must be finite and non-negative.
 * \param vertex_in_weights Numeric vector containing vertex in-weights for
 *    directed graphs. If set to \c NULL, in-weights are assumed to be the same
 *    as out-weights, which effectively ignores edge directions.
 *    Must be \c NULL for undirected graphs.
 * \param max_memberships The maximum number of communities to which a vertex
 *    may belong. If this is 1, the classical disjoint Leiden algorithm is
 *    used. Values greater than 1 enable overlapping community detection,
 *    require the \p memberships output, and must not exceed the vertex count.
 * \param start If true, start from the supplied \p membership or
 *    \p memberships instead of from a singleton partition or cover.
 * \param n_iterations Iterate the core Leiden algorithm the indicated number
 *    of times. If this is a negative number, iteration continues until a
 *    local-moving certificate sweep finds no strict (disjoint) or
 *    tolerance-level (overlapping) unilateral improvement. Positive budgets
 *    may stop before this sweep. Every overlapping multilevel proposal is
 *    nevertheless checked: the projected cover is retained only if it
 *    improves original-space quality beyond the numerical margin over the
 *    cover reached by the iteration's local moving, which is otherwise
 *    restored. Two
 *    iterations are often sufficient for ordinary use, thus 2 is a
 *    reasonable default.
 * \param beta The randomness used in the refinement step when merging. A small
 *    amount of randomness (\c beta = 0.01) typically works well. The
 *    overlapping path requires a finite, non-negative value.
 * \param allow_isolation Whether the local-moving phase may create a new
 *    isolated community or cover membership. When false, the local mover
 *    instead considers one extreme-mass omitted existing community so that
 *    a completed sweep is a hedonic best response over all active communities.
 * \param local_move_only If true, run only the local-moving phase. If false,
 *    also run refinement and aggregation. In overlapping mode, every
 *    multilevel proposal is guarded in original-graph quality units.
 * \param membership The disjoint membership vector. It is used as the initial
 *    partition when \p start is true and is updated in place. It may be NULL
 *    when using the overlapping interface.
 * \param memberships The overlapping membership list, with one sorted,
 *    duplicate-free, non-empty vector per vertex. It is required when
 *    \p max_memberships is greater than 1 and may also be used as the output
 *    form for the disjoint path.
 * \param nb_clusters The number of clusters contained in the final \p membership
 *    or \p memberships. If \c NULL, the number of clusters will not be returned.
 * \param quality The quality of the partition, in terms of the objective
 *    function as included in the documentation. Overlapping quality is the
 *    original-graph unit-l2 CPM potential divided by original total edge
 *    weight; zero-total-weight inputs are rejected. If \c NULL the quality
 *    will not be calculated.
 * \return Error code.
 *
 * The classical disjoint implementation is near linear on sparse graphs in
 * typical use. Overlapping local moving additionally depends on membership
 * incidences and candidate sorting. Multilevel overlapping mode materializes
 * up to sum_(uv in E) k_u k_v token edges and preflights this expansion.
 *
 * \sa \ref igraph_community_leiden_simple() for a simplified interface
 * that allows specifying an objective function directly and does not require
 * vertex weights; \ref igraph_community_leiden_with_constraints() for
 * global community-count constraints.
 *
 * \example examples/simple/igraph_community_leiden.c
 */
igraph_error_t igraph_community_leiden(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        igraph_real_t resolution,
        igraph_real_t beta,
        igraph_int_t max_memberships,
        igraph_bool_t start,
        igraph_int_t n_iterations,
        igraph_bool_t allow_isolation,
        igraph_bool_t local_move_only,
        igraph_vector_int_t *membership,
        igraph_vector_int_list_t *memberships,
        igraph_int_t *nb_clusters,
        igraph_real_t *quality) {
    return igraph_community_leiden_with_constraints(
               graph, edge_weights, vertex_out_weights, vertex_in_weights,
               resolution, beta, max_memberships,
               /* max_total_communities = */ -1, /* n_communities = */ -1,
               start, n_iterations, allow_isolation, local_move_only,
               membership, memberships, nb_clusters, quality);
}

/* -----------------------------------------------------------------------------
 * Section 5.2  igraph_community_leiden_with_constraints
 * -----------------------------------------------------------------------------
 */

/* Validates max_memberships and the count limits; negative limits become -1
 * (disabled). */
static igraph_error_t leiden_check_counts(igraph_int_t max_memberships,
                                          igraph_int_t *max_total_communities,
                                          igraph_int_t *n_communities) {
    if (max_memberships < 1) {
        IGRAPH_ERROR("max_memberships must be at least 1.", IGRAPH_EINVAL);
    }
    if (*max_total_communities < 0) {
        *max_total_communities = -1;
    }
    if (*n_communities < 0) {
        *n_communities = -1;
    }
    if (*max_total_communities == 0 || *n_communities == 0) {
        IGRAPH_ERROR("Community-count constraints must be positive (or negative to disable them).",
                     IGRAPH_EINVAL);
    }
    if (*max_total_communities > 0 && *n_communities > *max_total_communities) {
        IGRAPH_ERROR("n_communities must not exceed max_total_communities.", IGRAPH_EINVAL);
    }
    return IGRAPH_SUCCESS;
}

/**
 * \function igraph_community_leiden_with_constraints
 * \brief Leiden algorithm with global community-count constraints.
 *
 * This function has the parameters and semantics of
 * \ref igraph_community_leiden(), plus two optional constraints on the number
 * of occupied communities (communities with at least one member) of every
 * state visited by local moving, including every aggregate level of the
 * multilevel phase and every token level of the overlapping multilevel phase.
 * Distinct communities with identical member sets count separately.
 *
 * </para><para>
 * With \p max_total_communities set, at most that many communities are
 * occupied: a new (empty) community is offered to a moving vertex only while
 * fewer communities are occupied. With \p n_communities set, exactly that
 * many communities are occupied: no community is created and the last member
 * of a community keeps it. In both cases the local mover also considers the
 * least massive omitted community whenever the constraint withholds the empty
 * community, so a completed sweep is a best response over the feasible
 * unilateral actions. For covers with an exact count, labels held by the
 * moving vertex alone are retained and the remaining labels are chosen by the
 * usual sorted-prefix rule. The resulting states are constrained unilateral
 * equilibria: the feasible deviations of a vertex depend on the others.
 *
 * </para><para>
 * Without a start state, a feasible start is built deterministically: with a
 * target K (the exact count, otherwise an upper bound smaller than the vertex
 * count) vertex v starts in community v mod K; an exact count K larger than
 * the vertex count (covers only) starts from singleton rows and assigns the
 * remaining labels round-robin, which requires K <= n * max_memberships. A
 * supplied start state that violates a constraint is rejected, not repaired.
 *
 * \param max_total_communities Upper bound on occupied communities; a
 *    negative value disables it and zero is invalid.
 * \param n_communities Exact number of occupied communities; a negative
 *    value disables it and zero is invalid. It must not exceed
 *    \p max_total_communities when both are set, must not exceed the vertex
 *    count for partitions, and must not exceed n * max_memberships for covers.
 *
 * See \ref igraph_community_leiden() for the remaining parameters.
 *
 * \return Error code: \c IGRAPH_EINVAL for invalid or infeasible constraints.
 */
igraph_error_t igraph_community_leiden_with_constraints(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        igraph_real_t resolution,
        igraph_real_t beta,
        igraph_int_t max_memberships,
        igraph_int_t max_total_communities,
        igraph_int_t n_communities,
        igraph_bool_t start,
        igraph_int_t n_iterations,
        igraph_bool_t allow_isolation,
        igraph_bool_t local_move_only,
        igraph_vector_int_t *membership,
        igraph_vector_int_list_t *memberships,
        igraph_int_t *nb_clusters,
        igraph_real_t *quality) {

    IGRAPH_CHECK(leiden_check_counts(max_memberships, &max_total_communities, &n_communities));

    if (max_memberships == 1) {
        const leiden_options_t options = {
            .resolution = resolution,
            .beta = beta,
            .allow_isolation = allow_isolation,
            .local_move_only = local_move_only,
            .max_total_communities = max_total_communities,
            .n_communities = n_communities,
            .tolerant = false
        };
        return leiden_disjoint_run(graph, edge_weights, vertex_out_weights, vertex_in_weights,
                                   &options, start, n_iterations, membership, memberships,
                                   nb_clusters, quality);
    }

    /* Overlapping path: undirected only. */
    if (igraph_is_directed(graph)) {
        IGRAPH_ERROR("Overlapping Leiden algorithm is only implemented for undirected graphs.", IGRAPH_EINVAL);
    }
    if (vertex_in_weights) {
        IGRAPH_ERROR("Vertex in-weights are not supported for undirected overlapping Leiden.",
                     IGRAPH_EINVAL);
    }
    IGRAPH_UNUSED(membership);
    return overlap_leiden_run(graph, edge_weights, vertex_out_weights, resolution, beta,
                              max_memberships, max_total_communities, n_communities,
                              start, n_iterations, allow_isolation, local_move_only,
                              memberships, nb_clusters, quality,
                              /* move_trace = */ NULL, /* projection_trace = */ NULL);
}

/* -----------------------------------------------------------------------------
 * Section 5.3  igraph_community_leiden_with_diagnostics
 * -----------------------------------------------------------------------------
 */

/**
 * \function igraph_community_leiden_with_diagnostics
 * \brief Runs overlapping Leiden and records opt-in validation traces.
 *
 * This diagnostic entry point has the same overlapping semantics as
 * \ref igraph_community_leiden(), but requires \p max_memberships greater
 * than one and returns two newly initialized matrices. The accepted-move
 * trace compares the mover's predicted unnormalized potential delta with a
 * direct original-graph recomputation after every accepted move. The
 * projection trace records original and token total edge weights separately,
 * verifies the frozen-multiplicity unnormalized identity, counts same-origin
 * token collisions, and records whether each projected proposal was committed
 * or restored by the original-space quality guard. The final two columns,
 * added in 1.0.0.5, count occupied labels after local moving and in the
 * projected proposal before rollback. They allow a consumer to verify the
 * guard's label-reducing tie rule; the preceding 19 columns are unchanged.
 *
 * This path is intended for bounded validation fixtures. Direct quality
 * recomputation after every accepted move is deliberately expensive. A
 * negative move-trace stage identifies a final certificate sweep; nonnegative
 * stages identify zero-based outer iterations. Both output matrices are
 * initialized by this function and must be destroyed by the caller.
 */
igraph_error_t igraph_community_leiden_with_diagnostics(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        igraph_real_t resolution,
        igraph_real_t beta,
        igraph_int_t max_memberships,
        igraph_bool_t start,
        igraph_int_t n_iterations,
        igraph_bool_t allow_isolation,
        igraph_bool_t local_move_only,
        igraph_vector_int_list_t *memberships,
        igraph_int_t *nb_clusters,
        igraph_real_t *quality,
        igraph_matrix_t *move_trace,
        igraph_matrix_t *projection_trace) {
    if (max_memberships <= 1) {
        IGRAPH_ERROR("Overlapping Leiden diagnostics require max_memberships > 1.",
                     IGRAPH_EINVAL);
    }
    if (!move_trace || !projection_trace) {
        IGRAPH_ERROR("Overlapping Leiden diagnostics require both trace outputs.",
                     IGRAPH_EINVAL);
    }
    IGRAPH_MATRIX_INIT_FINALLY(move_trace, 0, IGRAPH_LEIDEN_OVERLAP_MOVE_TRACE_WIDTH);
    IGRAPH_MATRIX_INIT_FINALLY(projection_trace, 0, IGRAPH_LEIDEN_OVERLAP_PROJECTION_TRACE_WIDTH);

    if (igraph_is_directed(graph)) {
        IGRAPH_ERROR("Overlapping Leiden algorithm is only implemented for undirected graphs.",
                     IGRAPH_EINVAL);
    }
    if (vertex_in_weights) {
        IGRAPH_ERROR("Vertex in-weights are not supported for undirected overlapping Leiden.",
                     IGRAPH_EINVAL);
    }

    IGRAPH_CHECK(overlap_leiden_run(graph, edge_weights, vertex_out_weights, resolution, beta,
                                    max_memberships, /* max_total_communities = */ -1,
                                    /* n_communities = */ -1, start, n_iterations,
                                    allow_isolation, local_move_only, memberships, nb_clusters,
                                    quality, move_trace, projection_trace));

    IGRAPH_FINALLY_CLEAN(2);
    return IGRAPH_SUCCESS;
}

/* -----------------------------------------------------------------------------
 * Section 5.4  igraph_community_leiden_simple
 * -----------------------------------------------------------------------------
 */

typedef struct {
    igraph_vector_t vertex_out_weights;
    igraph_vector_t vertex_in_weights;     /* directed graphs only */
    igraph_vector_int_t owned_membership;  /* when no membership vector is given */
} leiden_simple_t;

static void leiden_simple_destroy(leiden_simple_t *simple) {
    igraph_vector_int_destroy(&simple->owned_membership);
    igraph_vector_destroy(&simple->vertex_in_weights);
    igraph_vector_destroy(&simple->vertex_out_weights);
}

/* Checks the edge weights and returns the smallest (infinity if NULL). */
static igraph_error_t leiden_simple_check_weights(const igraph_t *graph,
                                                  const igraph_vector_t *weights,
                                                  igraph_real_t *min_weight) {
    const igraph_int_t ecount = igraph_ecount(graph);

    *min_weight = IGRAPH_INFINITY;
    if (!weights) {
        return IGRAPH_SUCCESS;
    }
    if (igraph_vector_size(weights) != ecount) {
        IGRAPH_ERROR("Edge weight vector length does not match number of edges.", IGRAPH_EINVAL);
    }
    for (igraph_int_t i = 0; i < ecount; i++) {
        const igraph_real_t w = VECTOR(*weights)[i];
        if (w < *min_weight) {
            *min_weight = w;
        }
        if (!isfinite(w)) {
            IGRAPH_ERRORF("Edge weights must not be infinite or NaN, got %g.", IGRAPH_EINVAL, w);
        }
    }
    return IGRAPH_SUCCESS;
}

/* The membership vector to optimize: the caller's (which must be valid when
 * starting from it, and is resized otherwise) or an owned one. */
static igraph_error_t leiden_simple_membership(leiden_simple_t *simple, igraph_int_t vcount,
                                               igraph_bool_t start,
                                               igraph_vector_int_t *membership,
                                               igraph_vector_int_t **p_membership) {
    if (start) {
        if (!membership) {
            IGRAPH_ERROR("Requesting to start the computation from a specific "
                         "community assignment, but no membership vector given.",
                         IGRAPH_EINVAL);
        }
        if (igraph_vector_int_size(membership) != vcount) {
            IGRAPH_ERRORF("Requesting to start the computation from a specific "
                          "community assignment, but the given membership vector "
                          "has a different size (%" IGRAPH_PRId " than the vertex "
                          "count (%" IGRAPH_PRId ").",
                          IGRAPH_EINVAL,
                          igraph_vector_int_size(membership), vcount);
        }
        *p_membership = membership;
    } else if (!membership) {
        IGRAPH_CHECK(igraph_vector_int_init(&simple->owned_membership, vcount));
        *p_membership = &simple->owned_membership;
    } else {
        IGRAPH_CHECK(igraph_vector_int_resize(membership, vcount));
        *p_membership = membership;
    }
    return IGRAPH_SUCCESS;
}

/* Modularity: vertex weights are the (out- and in-) strengths and the
 * resolution is divided by their sum (2m, or m if directed). */
static igraph_error_t leiden_simple_modularity(const igraph_t *graph,
                                               const igraph_vector_t *weights,
                                               igraph_real_t min_weight,
                                               leiden_simple_t *simple,
                                               igraph_real_t *resolution) {
    if (min_weight < 0) {
        IGRAPH_ERRORF("Edge weights must not be negative for Leiden community "
                      "detection with modularity objective function, got %g.",
                      IGRAPH_EINVAL, min_weight);
    }
    IGRAPH_CHECK(igraph_strength(graph, &simple->vertex_out_weights,
                                 igraph_vss_all(), IGRAPH_OUT, IGRAPH_LOOPS, weights));
    if (igraph_is_directed(graph)) {
        IGRAPH_CHECK(igraph_strength(graph, &simple->vertex_in_weights,
                                     igraph_vss_all(), IGRAPH_IN, IGRAPH_LOOPS, weights));
    }
    *resolution /= igraph_vector_sum(&simple->vertex_out_weights);
    return IGRAPH_SUCCESS;
}

/* CPM and ER: unit vertex weights. */
static void leiden_simple_unit_weights(const igraph_t *graph, leiden_simple_t *simple) {
    igraph_vector_fill(&simple->vertex_out_weights, 1);
    if (igraph_is_directed(graph)) {
        igraph_vector_fill(&simple->vertex_in_weights, 1);
    }
}

/* ER: unit vertex weights, resolution times the weighted density. Loops are
 * allowed because aggregation effectively creates them. */
static igraph_error_t leiden_simple_erdos_renyi(const igraph_t *graph,
                                                const igraph_vector_t *weights,
                                                igraph_real_t min_weight,
                                                leiden_simple_t *simple,
                                                igraph_real_t *resolution) {
    igraph_real_t p;

    if (min_weight < 0) {
        IGRAPH_ERRORF("Edge weights must not be negative for Leiden community "
                      "detection with ER objective function, got %g.",
                      IGRAPH_EINVAL, min_weight);
    }
    leiden_simple_unit_weights(graph, simple);
    IGRAPH_CHECK(igraph_density(graph, weights, &p, /* loops */ true));
    *resolution *= p;
    return IGRAPH_SUCCESS;
}

/* Sets the vertex weights and resolution that implement `objective`. */
static igraph_error_t leiden_simple_objective(const igraph_t *graph,
                                              const igraph_vector_t *weights,
                                              igraph_leiden_objective_t objective,
                                              igraph_real_t min_weight,
                                              leiden_simple_t *simple,
                                              igraph_real_t *resolution) {
    switch (objective) {
    case IGRAPH_LEIDEN_OBJECTIVE_MODULARITY:
        return leiden_simple_modularity(graph, weights, min_weight, simple, resolution);
    case IGRAPH_LEIDEN_OBJECTIVE_CPM:
        leiden_simple_unit_weights(graph, simple);
        return IGRAPH_SUCCESS;
    case IGRAPH_LEIDEN_OBJECTIVE_ER:
        return leiden_simple_erdos_renyi(graph, weights, min_weight, simple, resolution);
    default:
        IGRAPH_ERROR("Invalid objective function for Leiden community detection.",
                     IGRAPH_EINVAL);
    }
}

/**
 * \function igraph_community_leiden_simple
 * \brief Finding community structure using the Leiden algorithm, simple interface.
 *
 * This is a simplified interface to \ref igraph_community_leiden() for
 * convenience purposes. Instead of requiring vertex weights, it allows
 * choosing from a set of objective functions to maximize. It implements
 * these objective functions by passing suitable vertex weights to
 * \ref igraph_community_leiden(), as explained in the documentation of
 * that function.
 *
 * \param graph The input graph. May be directed or undirected.
 * \param weights The edge weights. If \c NULL, all weights are assumed to be 1.
 * \param objective The objective function to maximize.
 *    \clist
 *    \cli IGRAPH_LEIDEN_OBJECTIVE_MODULARITY
 *      Use the generalized modularity, defined as
 *      <code>Q = 1/(2m) sum_ij (A_ij - γ k_i k_j / (2m)) δ(c_i, c_j)</code>
 *      for undirected graphs and as
 *      <code>Q = 1/m sum_ij (A_ij - γ k^out_i k^in_j / m) δ(c_i, c_j)</code>
 *      for directed graphs. This effectively uses a multigraph configuration
 *      model as the null model. Edge weights must not be negative.
 *    \cli IGRAPH_LEIDEN_OBJECTIVE_CPM
 *      Use the constant Potts model, whose objective function is defined as
 *      <code>Q = 1/(2m) sum_ij (A_ij - γ) δ(c_i, c_j)</code>
 *      for undirected graphs and as
 *      <code>Q = 1/m sum_ij (A_ij - γ) δ(c_i, c_j)</code>
 *      for directed graphs. Edge weights are allowed to be negative.
 *      Edge directions have no impact on the result.
 *    \cli IGRAPH_LEIDEN_OBJECTIVE_ER
 *      Use an objective function based on the multigraph Erdős-Rényi G(n,p)
 *      null model, defined as
 *      <code>Q = 1/(2m) sum_ij (A_ij - γ p) δ(c_i, c_j)</code>
 *      for undirected graphs and as
 *      <code>Q = 1/m sum_ij (A_ij - γ p) δ(c_i, c_j)</code>
 *      for directed graphs. \c p is the weighted density, i.e. the average
 *      link strength between all vertex pairs (whether adjacent or not).
 *      Edge weights must not be negative. Edge directions have no impact on
 *      the result.
 *    \endclist
 *    In the above formulas, \c A is the adjacency matrix, \c m is the total
 *    edge weight, \c k are the (out- and in-) degrees, \c γ is the resolution
 *    parameter, and <code>δ(c_i, c_j)</code> is 1 if vertices \c i and \c j
 *    are in the same community and 0 otherwise. Edge directions are only
 *    relevant with \c IGRAPH_LEIDEN_OBJECTIVE_MODULARITY. The other two
 *    objective functions are equivalent between directed and undirected graphs:
 *    the formal difference is due to each edge being included twice in
 *    undirected (symmetric) adjacency matrices.
 * \param resolution The resolution parameter, which is represented by γ in
 *    the objective functions detailed above.
 * \param beta The randomness used in the refinement step when merging. A small
 *    amount of randomness (\c beta = 0.01) typically works well.
 * \param start Start from membership vector. If this is true, the optimization
 *    will start from the provided membership vector. If this is false, the
 *    optimization will start from a singleton partition.
 * \param n_iterations Iterate the core Leiden algorithm the indicated number
 *    of times. If this is a negative number, it will continue iterating until
 *    an iteration did not change the clustering. Two iterations are often
 *    sufficient, thus 2 is a reasonable default.
 * \param membership The membership vector. If \p start is set to \c false,
 *    it will be resized appropriately. If \p start is \c true, it must be
 *    a valid membership vector for the given \p graph.
 * \param nb_clusters The number of clusters contained in the final \p membership.
 *    If \c NULL, the number of clusters will not be returned.
 * \param quality The quality of the partition, in terms of the objective
 *    function selected by \p objective. If \c NULL the quality will
 *    not be calculated.
 * \return Error code.
 *
 * Time complexity: near linear on sparse graphs.
 *
 * \sa \ref igraph_community_leiden() for a more flexible interface that
 * allows specifying raw vertex weights.
 */
igraph_error_t igraph_community_leiden_simple(
        const igraph_t *graph,
        const igraph_vector_t *weights,
        igraph_leiden_objective_t objective,
        igraph_real_t resolution,
        igraph_real_t beta,
        igraph_bool_t start,
        igraph_int_t n_iterations,
        igraph_vector_int_t *membership,
        igraph_int_t *nb_clusters,
        igraph_real_t *quality) {

    const igraph_int_t vcount = igraph_vcount(graph);
    const igraph_bool_t directed = igraph_is_directed(graph);
    leiden_simple_t simple = { .vertex_out_weights = { .stor_begin = NULL } };
    igraph_vector_int_t *p_membership;
    igraph_real_t min_weight;

    IGRAPH_CHECK(leiden_simple_check_weights(graph, weights, &min_weight));

    IGRAPH_FINALLY(leiden_simple_destroy, &simple);
    IGRAPH_CHECK(igraph_vector_init(&simple.vertex_out_weights, vcount));
    if (directed) {
        IGRAPH_CHECK(igraph_vector_init(&simple.vertex_in_weights, vcount));
    }
    IGRAPH_CHECK(leiden_simple_membership(&simple, vcount, start, membership, &p_membership));
    IGRAPH_CHECK(leiden_simple_objective(graph, weights, objective, min_weight, &simple,
                                         &resolution));

    IGRAPH_CHECK(igraph_community_leiden(
        graph, weights,
        &simple.vertex_out_weights, directed ? &simple.vertex_in_weights : NULL,
        resolution, beta,
        /*max_memberships=*/ 1, start, n_iterations,
        /*allow_isolation=*/ true, /*local_move_only=*/ false,
        p_membership, /*memberships=*/ NULL, nb_clusters, quality));

    leiden_simple_destroy(&simple);
    IGRAPH_FINALLY_CLEAN(1);
    return IGRAPH_SUCCESS;
}

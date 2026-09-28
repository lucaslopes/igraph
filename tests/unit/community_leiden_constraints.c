/*
   igraph library.
   Copyright (C) 2026  The igraph development team <igraph@igraph.org>

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

/* Community-count constraints of igraph_community_leiden_with_constraints().
 *
 * For every call with a negative iteration budget this test checks
 *   (1) the count invariant (at most / exactly K occupied communities), and
 *   (2) constrained unilateral stability: no vertex has a feasible bounded
 *       replacement of its label set that improves its utility, where
 *       feasibility means that the deviation keeps the count constraint and
 *       uses a new label only when isolation is allowed.
 * Stability is checked by enumerating every feasible label set, independently
 * of the sparse candidate set used by the implementation. */

#include <igraph.h>

#include "test_utilities.h"

#include <math.h>

#define MAX_LABELS 64

typedef struct {
    igraph_int_t n;
    igraph_int_t labels;
    igraph_real_t mass[MAX_LABELS];
    igraph_int_t holders[MAX_LABELS];
} cover_state_t;

static void build_state(const igraph_vector_int_list_t *rows, igraph_int_t n, cover_state_t *st) {
    st->n = n;
    st->labels = 0;
    for (igraph_int_t c = 0; c < MAX_LABELS; c++) {
        st->mass[c] = 0.0;
        st->holders[c] = 0;
    }
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(rows, v);
        const igraph_int_t k = igraph_vector_int_size(row);
        for (igraph_int_t i = 0; i < k; i++) {
            const igraph_int_t c = VECTOR(*row)[i];
            IGRAPH_ASSERT(c >= 0 && c < MAX_LABELS);
            st->mass[c] += 1.0 / sqrt((igraph_real_t) k);
            st->holders[c]++;
            if (c + 1 > st->labels) {
                st->labels = c + 1;
            }
        }
    }
}

static igraph_int_t occupied(const cover_state_t *st) {
    igraph_int_t count = 0;
    for (igraph_int_t c = 0; c < st->labels; c++) {
        count += st->holders[c] > 0;
    }
    return count;
}

/* Largest improvement of vertex v over its feasible bounded replacements. */
static igraph_real_t best_feasible_regret(
        const igraph_t *graph, const igraph_vector_int_list_t *rows,
        const cover_state_t *st, igraph_int_t v, igraph_real_t gamma,
        igraph_int_t max_memberships, igraph_bool_t allow_isolation,
        igraph_int_t max_total, igraph_int_t exact) {
    const igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(rows, v);
    const igraph_int_t k = igraph_vector_int_size(row);
    const igraph_int_t count = occupied(st);
    igraph_real_t gain[MAX_LABELS + 1], support[MAX_LABELS];
    igraph_bool_t own[MAX_LABELS];
    igraph_int_t universe = st->labels + 1; /* last index = one fresh label */
    igraph_real_t current = 0.0, best = -INFINITY;
    igraph_vector_int_t neis;

    for (igraph_int_t c = 0; c < st->labels; c++) {
        support[c] = 0.0;
        own[c] = igraph_vector_int_contains(row, c);
    }
    igraph_vector_int_init(&neis, 0);
    igraph_neighbors(graph, &neis, v, IGRAPH_ALL, IGRAPH_NO_LOOPS, IGRAPH_MULTIPLE);
    for (igraph_int_t i = 0; i < igraph_vector_int_size(&neis); i++) {
        const igraph_vector_int_t *urow = igraph_vector_int_list_get_ptr(rows, VECTOR(neis)[i]);
        for (igraph_int_t j = 0; j < igraph_vector_int_size(urow); j++) {
            support[VECTOR(*urow)[j]] += 1.0 / sqrt((igraph_real_t) igraph_vector_int_size(urow));
        }
    }
    igraph_vector_int_destroy(&neis);
    for (igraph_int_t c = 0; c < st->labels; c++) {
        const igraph_real_t other = st->mass[c] - (own[c] ? 1.0 / sqrt((igraph_real_t) k) : 0.0);
        gain[c] = support[c] - gamma * other;
        if (own[c]) {
            current += gain[c];
        }
    }
    gain[st->labels] = 0.0;
    current /= sqrt((igraph_real_t) k);

    /* Enumerate label sets over the universe by bitmask. */
    IGRAPH_ASSERT(universe <= 20);
    for (igraph_int_t mask = 1; mask < ((igraph_int_t) 1 << universe); mask++) {
        igraph_int_t size = 0, dropped_exclusive = 0, fresh = 0;
        igraph_real_t sum = 0.0;
        for (igraph_int_t c = 0; c < universe; c++) {
            if (mask & ((igraph_int_t) 1 << c)) {
                size++;
                sum += gain[c];
            }
        }
        if (size > max_memberships) {
            continue;
        }
        fresh = (mask >> st->labels) & 1;
        if (fresh && !allow_isolation) {
            continue;
        }
        for (igraph_int_t c = 0; c < st->labels; c++) {
            if (own[c] && st->holders[c] == 1 && !(mask & ((igraph_int_t) 1 << c))) {
                dropped_exclusive++;
            }
            if (!own[c] && st->holders[c] == 0 && (mask & ((igraph_int_t) 1 << c))) {
                fresh = 1; /* an emptied label behaves like a new one */
            }
        }
        {
            const igraph_int_t new_count = count - dropped_exclusive + fresh;
            if (max_total > 0 && new_count > max_total) {
                continue;
            }
            if (exact > 0 && new_count != exact) {
                continue;
            }
        }
        if (sum / sqrt((igraph_real_t) size) > best) {
            best = sum / sqrt((igraph_real_t) size);
        }
    }
    return (best - current) / fmax(1.0, fmax(fabs(best), fabs(current)));
}

static void check_run(const igraph_t *graph, igraph_real_t gamma, igraph_int_t max_memberships,
                      igraph_bool_t allow_isolation, igraph_bool_t local_move_only,
                      igraph_int_t max_total, igraph_int_t exact,
                      igraph_int_t *checked) {
    const igraph_int_t n = igraph_vcount(graph);
    igraph_vector_int_list_t rows;
    igraph_vector_int_t membership;
    igraph_int_t nb_clusters;
    igraph_real_t quality;
    cover_state_t st;

    igraph_vector_int_list_init(&rows, 0);
    igraph_vector_int_init(&membership, 0);
    IGRAPH_ASSERT(igraph_community_leiden_with_constraints(
        graph, NULL, NULL, NULL, gamma, 0.01, max_memberships, max_total, exact,
        /* start = */ false, /* n_iterations = */ -1, allow_isolation, local_move_only,
        max_memberships == 1 ? &membership : NULL, &rows, &nb_clusters, &quality)
        == IGRAPH_SUCCESS);
    build_state(&rows, n, &st);
    IGRAPH_ASSERT(occupied(&st) == nb_clusters);
    if (max_total > 0) {
        IGRAPH_ASSERT(nb_clusters <= max_total);
    }
    if (exact > 0) {
        IGRAPH_ASSERT(nb_clusters == exact);
    }
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_real_t regret = best_feasible_regret(
            graph, &rows, &st, v, gamma, max_memberships, allow_isolation, max_total, exact);
        if (regret > 1e-9) {
            printf("n=%" IGRAPH_PRId " gamma=%g M=%" IGRAPH_PRId " iso=%d local=%d max_total=%"
                   IGRAPH_PRId " exact=%" IGRAPH_PRId ": vertex %" IGRAPH_PRId " regret %g\n",
                   n, gamma, max_memberships, (int) allow_isolation, (int) local_move_only,
                   max_total, exact, v, regret);
            IGRAPH_FATAL("Constrained result is not a constrained unilateral equilibrium.");
        }
    }
    (*checked)++;
    igraph_vector_int_destroy(&membership);
    igraph_vector_int_list_destroy(&rows);
}

static void test_input_contract(void) {
    igraph_t graph;
    igraph_vector_int_list_t rows;
    igraph_vector_int_t membership;

    igraph_small(&graph, 4, IGRAPH_UNDIRECTED, 0, 1, 1, 2, 2, 3, -1);
    igraph_vector_int_list_init(&rows, 0);
    igraph_vector_int_init(&membership, 0);

    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 2,
                0, -1, false, -1, true, true, NULL, &rows, NULL, NULL), IGRAPH_EINVAL);
    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 2,
                -1, 0, false, -1, true, true, NULL, &rows, NULL, NULL), IGRAPH_EINVAL);
    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 2,
                2, 3, false, -1, true, true, NULL, &rows, NULL, NULL), IGRAPH_EINVAL);
    /* Exact counts above n are infeasible for partitions ... */
    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 1,
                -1, 5, false, -1, true, true, &membership, NULL, NULL, NULL), IGRAPH_EINVAL);
    /* ... and above n * max_memberships for covers. */
    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 2,
                -1, 9, false, -1, true, true, NULL, &rows, NULL, NULL), IGRAPH_EINVAL);

    /* A supplied start violating a constraint is rejected, not repaired. */
    igraph_vector_int_resize(&membership, 4);
    VECTOR(membership)[0] = 0; VECTOR(membership)[1] = 1;
    VECTOR(membership)[2] = 2; VECTOR(membership)[3] = 3;
    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 1,
                3, -1, true, -1, true, true, &membership, NULL, NULL, NULL), IGRAPH_EINVAL);
    VECTOR(membership)[0] = 0; VECTOR(membership)[1] = 0;
    VECTOR(membership)[2] = 1; VECTOR(membership)[3] = 1;
    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 1,
                -1, 3, true, -1, true, true, &membership, NULL, NULL, NULL), IGRAPH_EINVAL);
    igraph_vector_int_list_resize(&rows, 4);
    for (igraph_int_t v = 0; v < 4; v++) {
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&rows, v), v);
    }
    CHECK_ERROR(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.1, 0.01, 2,
                2, -1, true, -1, true, true, NULL, &rows, NULL, NULL), IGRAPH_EINVAL);

    igraph_vector_int_destroy(&membership);
    igraph_vector_int_list_destroy(&rows);
    igraph_destroy(&graph);
    printf("Constraint input contract: OK\n");
}

/* A bound that can never bind must reproduce the unconstrained call. */
static void test_non_binding_bound_is_identity(void) {
    igraph_t graph;

    igraph_rng_seed(igraph_rng_default(), 7);
    igraph_erdos_renyi_game_gnp(&graph, 40, 0.15, IGRAPH_UNDIRECTED, IGRAPH_SIMPLE_SW, false);
    for (igraph_int_t mode = 0; mode < 4; mode++) {
        const igraph_bool_t local = mode & 1, iso = (mode >> 1) & 1;
        igraph_vector_int_list_t a, b;
        igraph_int_t na, nb;
        igraph_real_t qa, qb;
        igraph_vector_int_list_init(&a, 0);
        igraph_vector_int_list_init(&b, 0);
        igraph_rng_seed(igraph_rng_default(), 11);
        IGRAPH_ASSERT(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.2, 0.01, 3, /* no count limits */ -1, -1, false, -1,
                      iso, local, NULL, &a, &na, &qa) == IGRAPH_SUCCESS);
        igraph_rng_seed(igraph_rng_default(), 11);
        IGRAPH_ASSERT(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.2, 0.01,
                      3, 40 * 3, -1, false, -1, iso, local, NULL, &b, &nb, &qb) == IGRAPH_SUCCESS);
        IGRAPH_ASSERT(na == nb && qa == qb);
        for (igraph_int_t v = 0; v < 40; v++) {
            IGRAPH_ASSERT(igraph_vector_int_all_e(igraph_vector_int_list_get_ptr(&a, v),
                                                  igraph_vector_int_list_get_ptr(&b, v)));
        }
        igraph_vector_int_list_destroy(&b);
        igraph_vector_int_list_destroy(&a);
    }
    igraph_destroy(&graph);
    printf("Non-binding bound reproduces the unconstrained call: OK\n");
}

/* The multilevel token stage must respect the bound as well. On two disjoint
 * edges in one label with M=2 and gamma=1/2, token refinement splits the
 * label when isolation is free; an upper bound of one label forbids it. */
static void test_multilevel_bound_witness(void) {
    igraph_t graph;
    igraph_vector_int_list_t rows;
    igraph_int_t nb;

    igraph_small(&graph, 4, IGRAPH_UNDIRECTED, 0, 1, 2, 3, -1);
    igraph_vector_int_list_init(&rows, 4);
    for (igraph_int_t v = 0; v < 4; v++) {
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&rows, v), 0);
    }
    igraph_rng_seed(igraph_rng_default(), 3);
    IGRAPH_ASSERT(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.5, 0.01, 2, /* no count limits */ -1, -1, true, 1,
                  false, false, NULL, &rows, &nb, NULL) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(nb == 2); /* isolation disabled locally, token stage splits */
    for (igraph_int_t v = 0; v < 4; v++) {
        igraph_vector_int_clear(igraph_vector_int_list_get_ptr(&rows, v));
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&rows, v), 0);
    }
    igraph_rng_seed(igraph_rng_default(), 3);
    IGRAPH_ASSERT(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.5, 0.01, 2,
                  1, -1, true, 1, false, false, NULL, &rows, &nb, NULL) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(nb == 1);
    igraph_vector_int_list_destroy(&rows);
    igraph_destroy(&graph);
    printf("Multilevel count witness: OK\n");
}

/* A zero iteration budget must still report the start state. */
static void test_zero_budget_outputs(void) {
    igraph_t graph;
    igraph_vector_int_t membership;
    igraph_vector_int_list_t rows;
    igraph_int_t nb = -12345;
    igraph_real_t quality = -777.0;

    igraph_small(&graph, 4, IGRAPH_UNDIRECTED, 0, 1, 2, 3, -1);
    igraph_vector_int_init(&membership, 0);
    IGRAPH_ASSERT(igraph_community_leiden(&graph, NULL, NULL, NULL, 0.5, 0.01, false, 0, &membership, &nb, &quality) == IGRAPH_SUCCESS);
    /* Singleton start: four clusters, no internal edges, CPM quality
     * (1/2m) sum_c (2 E_c - gamma n_c^2) = -4 * 0.5 / 4. */
    IGRAPH_ASSERT(nb == 4);
    IGRAPH_ASSERT(fabs(quality + 0.5) < 1e-12);

    /* A supplied start is reindexed and scored as given. */
    VECTOR(membership)[0] = 7; VECTOR(membership)[1] = 7;
    VECTOR(membership)[2] = 3; VECTOR(membership)[3] = 3;
    IGRAPH_ASSERT(igraph_community_leiden(&graph, NULL, NULL, NULL, 0.5, 0.01, true, 0, &membership, &nb, &quality) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(nb == 2);
    IGRAPH_ASSERT(VECTOR(membership)[0] == VECTOR(membership)[1]);
    IGRAPH_ASSERT(VECTOR(membership)[2] == VECTOR(membership)[3]);
    IGRAPH_ASSERT(fabs(quality - (2 * 2 - 0.5 * 8) / 4.0) < 1e-12);

    /* The overlapping path already reported its start state. */
    igraph_vector_int_list_init(&rows, 0);
    nb = -12345;
    IGRAPH_ASSERT(igraph_community_leiden_with_constraints(&graph, NULL, NULL, NULL, 0.5, 0.01, 2, /* no count limits */ -1, -1, false, 0,
                  true, false, NULL, &rows, &nb, &quality) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(nb == 4);

    igraph_vector_int_list_destroy(&rows);
    igraph_vector_int_destroy(&membership);
    igraph_destroy(&graph);
    printf("Zero-budget outputs: OK\n");
}

int main(void) {
    const igraph_real_t resolutions[] = { 0.0, 0.15, 0.5, 1.0, -0.3 };
    igraph_int_t checked = 0;

    test_input_contract();
    test_zero_budget_outputs();
    test_non_binding_bound_is_identity();
    test_multilevel_bound_witness();

    igraph_rng_seed(igraph_rng_default(), 20260927);
    for (igraph_int_t trial = 0; trial < 60; trial++) {
        igraph_t graph;
        const igraph_int_t n = RNG_INTEGER(3, 6);
        igraph_erdos_renyi_game_gnp(&graph, n, RNG_UNIF(0.3, 0.8), IGRAPH_UNDIRECTED,
                                    IGRAPH_SIMPLE_SW, false);
        if (igraph_ecount(&graph) == 0) {
            igraph_add_edge(&graph, 0, 1);
        }
        for (igraph_int_t r = 0; r < (igraph_int_t) (sizeof(resolutions) / sizeof(resolutions[0])); r++) {
            for (igraph_int_t M = 1; M <= 3; M++) {
                for (igraph_int_t mode = 0; mode < 4; mode++) {
                    const igraph_bool_t iso = mode & 1, local = (mode >> 1) & 1;
                    for (igraph_int_t K = 1; K <= n * M && K <= 12; K++) {
                        if (K <= n || M > 1) {
                            check_run(&graph, resolutions[r], M, iso, local, -1, K, &checked);
                        }
                        if (K <= n) {
                            check_run(&graph, resolutions[r], M, iso, local, K, -1, &checked);
                        }
                    }
                }
            }
        }
        igraph_destroy(&graph);
    }
    IGRAPH_ASSERT(checked > 10000);
    printf("Exhaustive constrained-equilibrium audit: OK\n");

    VERIFY_FINALLY_STACK();
    return 0;
}

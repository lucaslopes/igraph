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

/* Compatibility contract of the Leiden entry points.
 *
 *   (1) igraph_community_leiden() keeps the igraph 1.0.0 signature and
 *       argument errors. With a non-negative resolution and non-negative
 *       vertex weights it computes exactly what the extended entry point
 *       computes with max_memberships = 1, no count limits, isolation
 *       allowed and the complete multilevel algorithm; otherwise the
 *       extended entry point completes the candidate set and may differ.
 *   (2) The compatibility matrix: partitions and covers x allow_isolation x
 *       local_move_only x zero/positive/negative budgets x fresh/supplied
 *       starts x unconstrained/at-most/exact counts x the weight domains of
 *       each mode. For every cell the diagnostic entry point returns the same
 *       result as the constrained entry point (recording never influences
 *       the computation), in full and in counters-only mode, and its traces
 *       and counters satisfy their documented invariants.
 *   (3) Every invalid cross-mode combination is a native error, also through
 *       the diagnostic entry point, with a clean FINALLY stack. */

#include <igraph.h>

#include "test_utilities.h"

#include <math.h>

enum { COUNT_NONE, COUNT_AT_MOST, COUNT_EXACT };

typedef struct {
    igraph_t graph;
    igraph_vector_t edge_weights, node_weights, in_weights;
    igraph_bool_t has_edge_weights, has_node_weights, has_in_weights;
    igraph_vector_int_t start_membership;
    igraph_vector_int_list_t start_cover;
    igraph_real_t resolution, beta;
    igraph_int_t max_memberships, max_total, exact, budget;
    igraph_bool_t start, isolation, local;
} instance_t;

typedef struct {
    igraph_error_t code;
    igraph_vector_int_t membership;
    igraph_vector_int_list_t memberships;
    igraph_int_t nb;
    igraph_real_t quality;
} result_t;

static void result_init(result_t *res) {
    res->code = IGRAPH_SUCCESS;
    res->nb = -1;
    res->quality = -1.0;
    igraph_vector_int_init(&res->membership, 0);
    igraph_vector_int_list_init(&res->memberships, 0);
}

static void result_destroy(result_t *res) {
    igraph_vector_int_list_destroy(&res->memberships);
    igraph_vector_int_destroy(&res->membership);
}

static igraph_bool_t same_real(igraph_real_t a, igraph_real_t b) {
    return (isnan(a) && isnan(b)) || a == b;
}

static void assert_same_result(const result_t *a, const result_t *b, igraph_bool_t cover) {
    IGRAPH_ASSERT(a->code == b->code);
    if (a->code != IGRAPH_SUCCESS) {
        return;
    }
    IGRAPH_ASSERT(a->nb == b->nb);
    IGRAPH_ASSERT(same_real(a->quality, b->quality));
    if (cover) {
        const igraph_int_t n = igraph_vector_int_list_size(&a->memberships);
        IGRAPH_ASSERT(n == igraph_vector_int_list_size(&b->memberships));
        for (igraph_int_t v = 0; v < n; v++) {
            IGRAPH_ASSERT(igraph_vector_int_all_e(
                igraph_vector_int_list_get_ptr(&a->memberships, v),
                igraph_vector_int_list_get_ptr(&b->memberships, v)));
        }
    } else {
        IGRAPH_ASSERT(igraph_vector_int_all_e(&a->membership, &b->membership));
    }
}

/* ---- instances --------------------------------------------------------- */

static igraph_real_t uniform(igraph_real_t lo, igraph_real_t hi) {
    return RNG_UNIF(lo, hi);
}

/* weights: 0 unit; 1 positive reals; 2 partitions: signed edge and vertex
 * weights, covers: non-negative weights with zero vertex weights. */
static void instance_init(instance_t *inst, igraph_int_t max_memberships, igraph_bool_t directed,
                          int weights, int count, igraph_bool_t start,
                          igraph_bool_t isolation, igraph_bool_t local, igraph_int_t budget) {
    const igraph_bool_t cover = max_memberships > 1;
    igraph_int_t n, m, k;

    n = RNG_INTEGER(6, 16);
    m = RNG_INTEGER(n, 3 * n);
    if (m > n * (n - 1) / 2) {
        m = n * (n - 1) / 2;
    }
    igraph_erdos_renyi_game_gnm(&inst->graph, n, m, directed, IGRAPH_SIMPLE_SW, false);
    if (!cover && RNG_INTEGER(0, 3) == 0) {
        igraph_add_edge(&inst->graph, 0, 0);  /* the disjoint domain allows loops */
    }
    m = igraph_ecount(&inst->graph);

    inst->max_memberships = max_memberships;
    inst->start = start;
    inst->isolation = isolation;
    inst->local = local;
    inst->budget = budget;
    inst->resolution = cover ? uniform(0.02, 0.6) : uniform(-0.1, 0.6);
    inst->beta = 0.01;

    inst->has_edge_weights = weights > 0;
    inst->has_node_weights = weights > 0;
    inst->has_in_weights = directed && weights > 0;
    igraph_vector_init(&inst->edge_weights, m);
    igraph_vector_init(&inst->node_weights, n);
    igraph_vector_init(&inst->in_weights, n);
    for (igraph_int_t e = 0; e < m; e++) {
        VECTOR(inst->edge_weights)[e] = weights == 2 && !cover ? uniform(-1.0, 2.0) : uniform(0.1, 2.0);
    }
    for (igraph_int_t v = 0; v < n; v++) {
        VECTOR(inst->node_weights)[v] =
            weights == 2 ? (cover ? (v % 3 == 0 ? 0.0 : uniform(0.5, 2.0)) : uniform(-0.5, 1.5))
                         : uniform(0.5, 2.0);
        VECTOR(inst->in_weights)[v] = uniform(0.5, 2.0);
    }

    inst->max_total = -1;
    inst->exact = -1;
    k = 2 + n % 3;
    if (count == COUNT_AT_MOST) {
        inst->max_total = k;
    } else if (count == COUNT_EXACT) {
        inst->exact = k;
    }

    /* A supplied start that satisfies the count: v mod k (plus a second
     * label for some cover rows); otherwise labels in [0, n/2]. */
    igraph_vector_int_init(&inst->start_membership, n);
    igraph_vector_int_list_init(&inst->start_cover, n);
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_int_t c = count == COUNT_NONE ? RNG_INTEGER(0, n / 2) : v % k;
        igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(&inst->start_cover, v);
        VECTOR(inst->start_membership)[v] = c;
        igraph_vector_int_push_back(row, c);
        if (cover && v % 2 == 0) {
            const igraph_int_t d = count == COUNT_NONE ? (c + 1) % (n / 2 + 1) : (c + 1) % k;
            if (d != c) {
                igraph_vector_int_push_back(row, d);
                igraph_vector_int_sort(row);
            }
        }
    }
    if (count == COUNT_NONE && !cover) {
        /* Supplied partitions need not be compact. */
        igraph_int_t unused;
        igraph_reindex_membership(&inst->start_membership, NULL, &unused);
    }
}

static void instance_destroy(instance_t *inst) {
    igraph_vector_int_list_destroy(&inst->start_cover);
    igraph_vector_int_destroy(&inst->start_membership);
    igraph_vector_destroy(&inst->in_weights);
    igraph_vector_destroy(&inst->node_weights);
    igraph_vector_destroy(&inst->edge_weights);
    igraph_destroy(&inst->graph);
}

static void prepare_result(const instance_t *inst, result_t *res) {
    igraph_vector_int_update(&res->membership, &inst->start_membership);
    igraph_vector_int_list_destroy(&res->memberships);
    if (inst->start && inst->max_memberships > 1) {
        igraph_vector_int_list_init_copy(&res->memberships, &inst->start_cover);
    } else {
        igraph_vector_int_list_init(&res->memberships, 0);
    }
}

static void run_constraints(const instance_t *inst, igraph_int_t seed, result_t *res) {
    const igraph_bool_t cover = inst->max_memberships > 1;

    prepare_result(inst, res);
    igraph_rng_seed(igraph_rng_default(), seed);
    res->code = igraph_community_leiden_with_constraints(
        &inst->graph, inst->has_edge_weights ? &inst->edge_weights : NULL,
        inst->has_node_weights ? &inst->node_weights : NULL,
        inst->has_in_weights ? &inst->in_weights : NULL,
        inst->resolution, inst->beta, inst->max_memberships, inst->max_total, inst->exact,
        inst->start, inst->budget, inst->isolation, inst->local,
        cover ? NULL : &res->membership, cover ? &res->memberships : NULL,
        &res->nb, &res->quality);
}

static void run_diagnostics(const instance_t *inst, igraph_int_t seed, result_t *res,
                            igraph_matrix_t *moves, igraph_matrix_t *projections,
                            igraph_vector_int_t *counters) {
    const igraph_bool_t cover = inst->max_memberships > 1;

    prepare_result(inst, res);
    igraph_rng_seed(igraph_rng_default(), seed);
    res->code = igraph_community_leiden_with_diagnostics(
        &inst->graph, inst->has_edge_weights ? &inst->edge_weights : NULL,
        inst->has_node_weights ? &inst->node_weights : NULL,
        inst->has_in_weights ? &inst->in_weights : NULL,
        inst->resolution, inst->beta, inst->max_memberships, inst->max_total, inst->exact,
        inst->start, inst->budget, inst->isolation, inst->local,
        cover ? NULL : &res->membership, cover ? &res->memberships : NULL,
        &res->nb, &res->quality, moves, projections, counters);
}

/* ---- trace invariants -------------------------------------------------- */

#define COUNTER(name) VECTOR(*counters)[IGRAPH_LEIDEN_COUNTER_##name]
#define MOVE(row, name) MATRIX(*moves, row, IGRAPH_LEIDEN_MOVE_##name)

static igraph_int_t levels_seen, signed_rows_seen, sweep_rows_seen, tied_seen;

static void check_counters(const instance_t *inst, const result_t *res,
                           const igraph_matrix_t *moves, const igraph_matrix_t *projections,
                           const igraph_vector_int_t *counters) {
    const igraph_bool_t cover = inst->max_memberships > 1;

    IGRAPH_ASSERT(igraph_vector_int_size(counters) == IGRAPH_LEIDEN_COUNTER_WIDTH);
    IGRAPH_ASSERT(COUNTER(SCHEMA_VERSION) == IGRAPH_LEIDEN_TRACE_SCHEMA_VERSION);
    IGRAPH_ASSERT(COUNTER(MAX_MEMBERSHIPS) == inst->max_memberships);
    IGRAPH_ASSERT(COUNTER(MAX_TOTAL_COMMUNITIES) == inst->max_total);
    IGRAPH_ASSERT(COUNTER(N_COMMUNITIES) == inst->exact);
    IGRAPH_ASSERT(COUNTER(VISITS) == COUNTER(ACCEPTED_MOVES) + COUNTER(REJECTED_VISITS));
    IGRAPH_ASSERT(COUNTER(PROPOSALS) == COUNTER(PROPOSALS_IMPROVED) +
                  COUNTER(PROPOSALS_TIED) + COUNTER(PROPOSALS_REJECTED));
    IGRAPH_ASSERT(COUNTER(MOVE_ROWS) == igraph_matrix_nrow(moves));
    IGRAPH_ASSERT(COUNTER(MOVE_ROWS) == COUNTER(ACCEPTED_MOVES));
    IGRAPH_ASSERT(COUNTER(PROJECTION_ROWS) == igraph_matrix_nrow(projections));
    IGRAPH_ASSERT(igraph_matrix_ncol(moves) == IGRAPH_LEIDEN_MOVE_TRACE_WIDTH);
    IGRAPH_ASSERT(igraph_matrix_ncol(projections) == IGRAPH_LEIDEN_OVERLAP_PROJECTION_TRACE_WIDTH);

    if (!cover || inst->local) {
        IGRAPH_ASSERT(COUNTER(PROPOSALS) == 0 && COUNTER(PROJECTION_ROWS) == 0);
    } else {
        IGRAPH_ASSERT(COUNTER(PROPOSALS) == COUNTER(PROJECTION_ROWS));
    }
    if (cover || inst->local) {
        IGRAPH_ASSERT(COUNTER(AGGREGATE_LEVELS) == 0);
    }
    levels_seen += COUNTER(AGGREGATE_LEVELS);
    tied_seen += COUNTER(PROPOSALS_TIED);

    if (inst->budget == 0) {
        IGRAPH_ASSERT(COUNTER(ITERATIONS) == 0 && COUNTER(VISITS) == 0);
    } else if (inst->budget > 0) {
        IGRAPH_ASSERT(COUNTER(ITERATIONS) >= 1 && COUNTER(ITERATIONS) <= inst->budget);
        IGRAPH_ASSERT(COUNTER(VISITS) >= igraph_vcount(&inst->graph));
    } else {
        IGRAPH_ASSERT(COUNTER(ITERATIONS) >= 1);
    }
    if (inst->budget >= 0 || inst->local) {
        IGRAPH_ASSERT(COUNTER(CERTIFICATE_SWEEPS) == 0);
    } else {
        IGRAPH_ASSERT(COUNTER(CERTIFICATE_SWEEPS) >= 1);
    }

    if (inst->max_total > 0) {
        IGRAPH_ASSERT(res->nb <= inst->max_total);
    }
    if (inst->exact > 0) {
        IGRAPH_ASSERT(res->nb == inst->exact);
    }
}

static void check_moves(const instance_t *inst, const igraph_matrix_t *moves,
                        const igraph_vector_int_t *counters) {
    const igraph_bool_t cover = inst->max_memberships > 1;
    const igraph_real_t weight = inst->has_edge_weights ?
                                 igraph_vector_sum(&inst->edge_weights) :
                                 (igraph_real_t) igraph_ecount(&inst->graph);

    for (igraph_int_t row = 0; row < igraph_matrix_nrow(moves); row++) {
        const igraph_int_t stage = (igraph_int_t) MOVE(row, STAGE);
        const igraph_int_t level = (igraph_int_t) MOVE(row, LEVEL);

        IGRAPH_ASSERT(MOVE(row, SEQUENCE) == row);
        IGRAPH_ASSERT(MOVE(row, PREDICTED_DELTA) > 0.0);
        IGRAPH_ASSERT(MOVE(row, ABS_ERROR) <= MOVE(row, TOLERANCE));
        IGRAPH_ASSERT(MOVE(row, ORIGINAL_WEIGHT) == weight);
        if (weight > 0.0) {
            IGRAPH_ASSERT(MOVE(row, QUALITY_AFTER) + 1e-9 >= MOVE(row, QUALITY_BEFORE));
        } else {
            signed_rows_seen++;
        }
        if (inst->budget >= 0) {
            IGRAPH_ASSERT(stage >= 0 && stage < inst->budget);
        } else if (stage < 0) {
            IGRAPH_ASSERT(-stage <= COUNTER(CERTIFICATE_SWEEPS));
            sweep_rows_seen++;
        }
        if (cover) {
            IGRAPH_ASSERT(level == 0);
            IGRAPH_ASSERT(MOVE(row, CARDINALITY_BEFORE) >= 1 &&
                          MOVE(row, CARDINALITY_BEFORE) <= inst->max_memberships);
            IGRAPH_ASSERT(MOVE(row, CARDINALITY_AFTER) >= 1 &&
                          MOVE(row, CARDINALITY_AFTER) <= inst->max_memberships);
        } else {
            IGRAPH_ASSERT(level >= 0 && (level == 0 || !inst->local));
            IGRAPH_ASSERT(MOVE(row, CARDINALITY_BEFORE) == 1 && MOVE(row, CARDINALITY_AFTER) == 1);
        }
        if (inst->max_total > 0) {
            IGRAPH_ASSERT(MOVE(row, OCCUPIED_BEFORE) <= inst->max_total);
            IGRAPH_ASSERT(MOVE(row, OCCUPIED_AFTER) <= inst->max_total);
        }
        if (inst->exact > 0) {
            IGRAPH_ASSERT(MOVE(row, OCCUPIED_BEFORE) == inst->exact);
            IGRAPH_ASSERT(MOVE(row, OCCUPIED_AFTER) == inst->exact);
        }
        IGRAPH_ASSERT(MOVE(row, OCCUPIED_AFTER) - MOVE(row, OCCUPIED_BEFORE) <= 1 + cover * inst->max_memberships);
    }
}

static void check_cell(const instance_t *inst, igraph_int_t seed) {
    const igraph_bool_t cover = inst->max_memberships > 1;
    result_t plain, full, compact;
    igraph_matrix_t moves, projections;
    igraph_vector_int_t counters, compact_counters;

    result_init(&plain);
    result_init(&full);
    result_init(&compact);

    run_constraints(inst, seed, &plain);
    IGRAPH_ASSERT(plain.code == IGRAPH_SUCCESS);

    run_diagnostics(inst, seed, &full, &moves, &projections, &counters);
    assert_same_result(&plain, &full, cover);
    check_counters(inst, &full, &moves, &projections, &counters);
    check_moves(inst, &moves, &counters);

    run_diagnostics(inst, seed, &compact, NULL, NULL, &compact_counters);
    assert_same_result(&plain, &compact, cover);
    for (igraph_int_t i = 0; i < IGRAPH_LEIDEN_COUNTER_WIDTH; i++) {
        if (i == IGRAPH_LEIDEN_COUNTER_MOVE_ROWS || i == IGRAPH_LEIDEN_COUNTER_PROJECTION_ROWS) {
            IGRAPH_ASSERT(VECTOR(compact_counters)[i] == 0);
        } else {
            IGRAPH_ASSERT(VECTOR(compact_counters)[i] == VECTOR(counters)[i]);
        }
    }

    igraph_vector_int_destroy(&compact_counters);
    igraph_vector_int_destroy(&counters);
    igraph_matrix_destroy(&projections);
    igraph_matrix_destroy(&moves);
    result_destroy(&compact);
    result_destroy(&full);
    result_destroy(&plain);
    VERIFY_FINALLY_STACK();
}

/* ---- (1) the igraph 1.0.0 entry point -------------------------------------- */

static void test_base_equals_extended_defaults(void) {
    static const igraph_int_t budgets[] = {0, 1, 2, -1};
    igraph_int_t cells = 0, equal_cells = 0, completed_cells = 0;

    for (igraph_int_t rep = 0; rep < 40; rep++) {
        for (int b = 0; b < 4; b++) {
            instance_t inst;
            result_t base, extended;
            const igraph_bool_t directed = rep % 3 == 1;

            igraph_rng_seed(igraph_rng_default(), 1000 + rep);
            instance_init(&inst, 1, directed, rep % 3, COUNT_NONE, rep % 2 == 0, true, false,
                          budgets[b]);
            result_init(&base);
            result_init(&extended);

            run_constraints(&inst, 7 * rep + b, &extended);

            prepare_result(&inst, &base);
            igraph_rng_seed(igraph_rng_default(), 7 * rep + b);
            base.code = igraph_community_leiden(
                &inst.graph, inst.has_edge_weights ? &inst.edge_weights : NULL,
                inst.has_node_weights ? &inst.node_weights : NULL,
                inst.has_in_weights ? &inst.in_weights : NULL,
                inst.resolution, inst.beta, inst.start, inst.budget,
                &base.membership, &base.nb, &base.quality);

            IGRAPH_ASSERT(base.code == IGRAPH_SUCCESS);
            if (inst.resolution >= 0.0 &&
                (!inst.has_node_weights || igraph_vector_min(&inst.node_weights) >= 0.0)) {
                assert_same_result(&extended, &base, false);
                equal_cells++;
            } else if (!igraph_vector_int_all_e(&extended.membership, &base.membership)) {
                /* The extended entry point completed the candidate set. */
                completed_cells++;
            }
            cells++;

            result_destroy(&extended);
            result_destroy(&base);
            instance_destroy(&inst);
        }
    }
    IGRAPH_ASSERT(cells == 160);
    IGRAPH_ASSERT(equal_cells > 60);
    IGRAPH_ASSERT(completed_cells > 0);
    printf("igraph 1.0.0 igraph_community_leiden equals the extended defaults: OK\n");
}

static void test_base_argument_errors(void) {
    igraph_t graph, directed;
    igraph_vector_int_t membership;
    igraph_vector_t weights;

    igraph_ring(&graph, 6, IGRAPH_UNDIRECTED, false, true);
    igraph_ring(&directed, 6, IGRAPH_DIRECTED, false, true);
    igraph_vector_int_init(&membership, 5);
    igraph_vector_init(&weights, 6);
    igraph_vector_fill(&weights, 1.0);

    CHECK_ERROR(igraph_community_leiden(&graph, NULL, NULL, NULL, 0.1, 0.01, true, 2,
                                        NULL, NULL, NULL), IGRAPH_EINVAL);
    CHECK_ERROR(igraph_community_leiden(&graph, NULL, NULL, NULL, 0.1, 0.01, false, 2,
                                        NULL, NULL, NULL), IGRAPH_EINVAL);
    CHECK_ERROR(igraph_community_leiden(&graph, NULL, NULL, NULL, 0.1, 0.01, true, 2,
                                        &membership, NULL, NULL), IGRAPH_EINVAL);
    CHECK_ERROR(igraph_community_leiden(&graph, NULL, &weights, &weights, 0.1, 0.01, false, 2,
                                        &membership, NULL, NULL), IGRAPH_EINVAL);
    igraph_vector_resize(&weights, 5);
    CHECK_ERROR(igraph_community_leiden(&graph, &weights, NULL, NULL, 0.1, 0.01, false, 2,
                                        &membership, NULL, NULL), IGRAPH_EINVAL);

    /* Without a start, the membership vector is resized; in-weights are
     * accepted for directed graphs. */
    igraph_vector_resize(&weights, 6);
    IGRAPH_ASSERT(igraph_community_leiden(&directed, NULL, &weights, &weights, 0.1, 0.01, false,
                                          2, &membership, NULL, NULL) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(igraph_vector_int_size(&membership) == 6);

    igraph_vector_destroy(&weights);
    igraph_vector_int_destroy(&membership);
    igraph_destroy(&directed);
    igraph_destroy(&graph);
    VERIFY_FINALLY_STACK();
    printf("igraph 1.0.0 igraph_community_leiden argument errors: OK\n");
}

/* ---- (2) the compatibility matrix --------------------------------------- */

static void test_compatibility_matrix(void) {
    static const igraph_int_t modes[] = {1, 2, 3};
    static const igraph_int_t budgets[] = {0, 1, 3, -1};
    igraph_int_t cells = 0, seed = 0;

    levels_seen = signed_rows_seen = sweep_rows_seen = tied_seen = 0;
    for (int mode = 0; mode < 3; mode++) {
        for (int isolation = 0; isolation < 2; isolation++) {
            for (int local = 0; local < 2; local++) {
                for (int b = 0; b < 4; b++) {
                    for (int start = 0; start < 2; start++) {
                        for (int count = COUNT_NONE; count <= COUNT_EXACT; count++) {
                            for (int weights = 0; weights < 3; weights++) {
                                for (int rep = 0; rep < 2; rep++) {
                                    instance_t inst;
                                    const igraph_bool_t directed = modes[mode] == 1 && rep == 1;
                                    igraph_rng_seed(igraph_rng_default(), 50000 + seed);
                                    instance_init(&inst, modes[mode], directed, weights, count,
                                                  start, isolation, local, budgets[b]);
                                    check_cell(&inst, seed);
                                    instance_destroy(&inst);
                                    cells++;
                                    seed++;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    IGRAPH_ASSERT(cells == 3 * 2 * 2 * 4 * 2 * 3 * 3 * 2);
    /* The battery reaches the rows the invariants are about. */
    IGRAPH_ASSERT(levels_seen > 0);
    IGRAPH_ASSERT(signed_rows_seen > 0);
    IGRAPH_ASSERT(sweep_rows_seen > 0);
    printf("compatibility matrix (%d cells, diagnostic = constrained result): OK\n",
           (int) cells);
}

/* ---- (3) invalid cross-mode combinations -------------------------------- */

typedef struct {
    const char *what;
    const igraph_t *graph;
    const igraph_vector_t *edge_weights, *node_weights, *in_weights;
    igraph_real_t resolution, beta;
    igraph_int_t max_memberships, max_total, exact;
    igraph_bool_t start, give_membership, give_memberships;
    const igraph_vector_int_list_t *start_cover;
} invalid_t;

static void check_invalid(const invalid_t *c) {
    igraph_vector_int_t membership;
    igraph_vector_int_list_t memberships;
    igraph_matrix_t moves, projections;
    igraph_vector_int_t counters;

    igraph_vector_int_init_range(&membership, 0, igraph_vcount(c->graph));
    if (c->start_cover) {
        igraph_vector_int_list_init_copy(&memberships, c->start_cover);
    } else {
        igraph_vector_int_list_init(&memberships, 0);
    }

    CHECK_ERROR(igraph_community_leiden_with_constraints(
        c->graph, c->edge_weights, c->node_weights, c->in_weights, c->resolution, c->beta,
        c->max_memberships, c->max_total, c->exact, c->start, 2, true, false,
        c->give_membership ? &membership : NULL, c->give_memberships ? &memberships : NULL,
        NULL, NULL), IGRAPH_EINVAL);
    CHECK_ERROR(igraph_community_leiden_with_diagnostics(
        c->graph, c->edge_weights, c->node_weights, c->in_weights, c->resolution, c->beta,
        c->max_memberships, c->max_total, c->exact, c->start, 2, true, false,
        c->give_membership ? &membership : NULL, c->give_memberships ? &memberships : NULL,
        NULL, NULL, &moves, &projections, &counters), IGRAPH_EINVAL);
    VERIFY_FINALLY_STACK();

    igraph_vector_int_list_destroy(&memberships);
    igraph_vector_int_destroy(&membership);
}

static void test_invalid_combinations(void) {
    igraph_t ring, directed, looped, empty;
    igraph_vector_t negative_edges, negative_nodes, ones6;
    igraph_vector_int_list_t bad_cover;

    igraph_ring(&ring, 6, IGRAPH_UNDIRECTED, false, true);
    igraph_ring(&directed, 6, IGRAPH_DIRECTED, false, true);
    igraph_ring(&looped, 6, IGRAPH_UNDIRECTED, false, true);
    igraph_add_edge(&looped, 2, 2);
    igraph_empty(&empty, 6, IGRAPH_UNDIRECTED);
    igraph_vector_init(&ones6, 6);
    igraph_vector_fill(&ones6, 1.0);
    igraph_vector_init_copy(&negative_edges, &ones6);
    VECTOR(negative_edges)[3] = -1.0;
    igraph_vector_init_copy(&negative_nodes, &ones6);
    VECTOR(negative_nodes)[1] = -1.0;
    /* A start cover with four labels, against an exact count of three. */
    igraph_vector_int_list_init(&bad_cover, 6);
    for (igraph_int_t v = 0; v < 6; v++) {
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&bad_cover, v), v % 4);
    }

    const invalid_t cases[] = {
        /* what, graph, ew, nw, in, gamma, beta, M, max_total, exact, start, membership, memberships, cover */
        {"cover of a directed graph", &directed, NULL, NULL, NULL, 0.1, 0.01, 2, -1, -1, false, false, true, NULL},
        {"cover with in-weights", &ring, NULL, NULL, &ones6, 0.1, 0.01, 2, -1, -1, false, false, true, NULL},
        {"cover with a membership vector", &ring, NULL, NULL, NULL, 0.1, 0.01, 2, -1, -1, false, true, true, NULL},
        {"cover without memberships", &ring, NULL, NULL, NULL, 0.1, 0.01, 2, -1, -1, false, false, false, NULL},
        {"cover with a negative edge weight", &ring, &negative_edges, NULL, NULL, 0.1, 0.01, 2, -1, -1, false, false, true, NULL},
        {"cover with a negative vertex weight", &ring, NULL, &negative_nodes, NULL, 0.1, 0.01, 2, -1, -1, false, false, true, NULL},
        {"cover of a graph with a loop", &looped, NULL, NULL, NULL, 0.1, 0.01, 2, -1, -1, false, false, true, NULL},
        {"cover of a graph without edges", &empty, NULL, NULL, NULL, 0.1, 0.01, 2, -1, -1, false, false, true, NULL},
        {"cover with max_memberships > n", &ring, NULL, NULL, NULL, 0.1, 0.01, 7, -1, -1, false, false, true, NULL},
        {"cover with an infinite resolution", &ring, NULL, NULL, NULL, IGRAPH_INFINITY, 0.01, 2, -1, -1, false, false, true, NULL},
        {"cover with a negative beta", &ring, NULL, NULL, NULL, 0.1, -1.0, 2, -1, -1, false, false, true, NULL},
        {"max_memberships = 0", &ring, NULL, NULL, NULL, 0.1, 0.01, 0, -1, -1, false, true, false, NULL},
        {"partition without outputs", &ring, NULL, NULL, NULL, 0.1, 0.01, 1, -1, -1, false, false, false, NULL},
        {"zero max_total_communities", &ring, NULL, NULL, NULL, 0.1, 0.01, 1, 0, -1, false, true, false, NULL},
        {"zero n_communities", &ring, NULL, NULL, NULL, 0.1, 0.01, 2, -1, 0, false, false, true, NULL},
        {"n_communities above max_total_communities", &ring, NULL, NULL, NULL, 0.1, 0.01, 1, 2, 3, false, true, false, NULL},
        {"partition n_communities above n", &ring, NULL, NULL, NULL, 0.1, 0.01, 1, -1, 7, false, true, false, NULL},
        {"cover n_communities above n * M", &ring, NULL, NULL, NULL, 0.1, 0.01, 2, -1, 13, false, false, true, NULL},
        {"cover start violating n_communities", &ring, NULL, NULL, NULL, 0.1, 0.01, 2, -1, 3, true, false, true, &bad_cover},
        {"cover start violating max_total_communities", &ring, NULL, NULL, NULL, 0.1, 0.01, 2, 3, -1, true, false, true, &bad_cover},
    };

    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
        check_invalid(&cases[i]);
    }

    igraph_vector_int_list_destroy(&bad_cover);
    igraph_vector_destroy(&negative_nodes);
    igraph_vector_destroy(&negative_edges);
    igraph_vector_destroy(&ones6);
    igraph_destroy(&empty);
    igraph_destroy(&looped);
    igraph_destroy(&directed);
    igraph_destroy(&ring);
    VERIFY_FINALLY_STACK();
    printf("invalid cross-mode combinations (%d cases, both extended entry points): OK\n",
           (int) (sizeof(cases) / sizeof(cases[0])));
}

int main(void) {
    igraph_set_error_handler(igraph_error_handler_ignore);

    test_base_equals_extended_defaults();
    test_base_argument_errors();
    test_compatibility_matrix();
    test_invalid_combinations();

    VERIFY_FINALLY_STACK();
    return 0;
}

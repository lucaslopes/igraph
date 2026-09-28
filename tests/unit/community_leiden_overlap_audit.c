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

/* Randomized audit of the Leiden local movers (disjoint and unit-l2 CPM).
 *
 * Every call with a negative iteration budget must return a cover in which
 * no vertex can improve its utility by more than a small tolerance through a
 * bounded replacement of its whole label set. This test recomputes that
 * best response independently, by brute force over *all* active labels (and
 * one fresh label when isolation is allowed), instead of the sparse
 * candidate set used by the implementation. It therefore checks candidate
 * completeness, the omitted-label selection for both resolution signs, the
 * prefix scan, and incremental mass bookkeeping together.
 *
 * Debug builds additionally cross-check every omitted-label query of the
 * mover against a linear scan. */

#include <igraph.h>

#include "test_utilities.h"

#include <float.h>
#include <math.h>
#include <stdlib.h>

static int cmp_desc(const void *a, const void *b) {
    const igraph_real_t x = *(const igraph_real_t *) a;
    const igraph_real_t y = *(const igraph_real_t *) b;
    return x > y ? -1 : (x < y ? 1 : 0);
}

/* Maximum over vertices of (best bounded response utility - current utility),
 * relative to max(1, |best|, |current|). */
static igraph_real_t max_relative_regret(
        const igraph_t *graph, const igraph_vector_t *edge_weights,
        const igraph_vector_t *node_weights, igraph_real_t gamma,
        igraph_int_t max_memberships, igraph_bool_t allow_isolation,
        const igraph_vector_int_list_t *memberships) {
    const igraph_int_t n = igraph_vcount(graph);
    const igraph_int_t m = igraph_ecount(graph);
    igraph_int_t labels = 0;
    igraph_vector_t mass, support, gains;
    igraph_real_t worst = 0.0;

    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(memberships, v);
        for (igraph_int_t i = 0; i < igraph_vector_int_size(row); i++) {
            if (VECTOR(*row)[i] + 1 > labels) {
                labels = VECTOR(*row)[i] + 1;
            }
        }
    }
    igraph_vector_init(&mass, labels);
    igraph_vector_init(&support, labels);
    igraph_vector_init(&gains, labels + 1);
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(row);
        const igraph_real_t w = node_weights ? VECTOR(*node_weights)[v] : 1.0;
        for (igraph_int_t i = 0; i < k; i++) {
            VECTOR(mass)[VECTOR(*row)[i]] += w / sqrt((igraph_real_t) k);
        }
    }

    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(row);
        const igraph_real_t w = node_weights ? VECTOR(*node_weights)[v] : 1.0;
        igraph_int_t count = 0, jmax;
        igraph_real_t current = 0.0, best = -INFINITY, prefix = 0.0, scale;

        igraph_vector_null(&support);
        for (igraph_int_t e = 0; e < m; e++) {
            igraph_int_t u;
            const igraph_vector_int_t *urow;
            if (IGRAPH_FROM(graph, e) == v) {
                u = IGRAPH_TO(graph, e);
            } else if (IGRAPH_TO(graph, e) == v) {
                u = IGRAPH_FROM(graph, e);
            } else {
                continue;
            }
            urow = igraph_vector_int_list_get_ptr(memberships, u);
            for (igraph_int_t i = 0; i < igraph_vector_int_size(urow); i++) {
                VECTOR(support)[VECTOR(*urow)[i]] +=
                    (edge_weights ? VECTOR(*edge_weights)[e] : 1.0) /
                    sqrt((igraph_real_t) igraph_vector_int_size(urow));
            }
        }
        for (igraph_int_t c = 0; c < labels; c++) {
            igraph_real_t other = VECTOR(mass)[c];
            if (igraph_vector_int_contains(row, c)) {
                other -= w / sqrt((igraph_real_t) k);
            }
            if (VECTOR(mass)[c] <= 0.0 && !igraph_vector_int_contains(row, c)) {
                /* An emptied label with zero mass: still an active label only
                 * if some vertex holds it; the returned cover is compact, so
                 * every label below `labels` is held by someone. */
            }
            VECTOR(gains)[count++] = VECTOR(support)[c] - gamma * w * other;
        }
        for (igraph_int_t i = 0; i < k; i++) {
            current += VECTOR(support)[VECTOR(*row)[i]] - gamma * w *
                       (VECTOR(mass)[VECTOR(*row)[i]] - w / sqrt((igraph_real_t) k));
        }
        current /= sqrt((igraph_real_t) k);
        if (allow_isolation) {
            VECTOR(gains)[count++] = 0.0;
        }
        qsort(VECTOR(gains), (size_t) count, sizeof(igraph_real_t), cmp_desc);
        jmax = count < max_memberships ? count : max_memberships;
        for (igraph_int_t j = 1; j <= jmax; j++) {
            prefix += VECTOR(gains)[j - 1];
            if (prefix / sqrt((igraph_real_t) j) > best) {
                best = prefix / sqrt((igraph_real_t) j);
            }
        }
        scale = fmax(1.0, fmax(fabs(best), fabs(current)));
        if ((best - current) / scale > worst) {
            worst = (best - current) / scale;
        }
    }

    igraph_vector_destroy(&gains);
    igraph_vector_destroy(&support);
    igraph_vector_destroy(&mass);
    return worst;
}

static void assert_valid_cover(const igraph_vector_int_list_t *memberships,
                               igraph_int_t n, igraph_int_t max_memberships,
                               igraph_int_t nb_clusters) {
    igraph_vector_bool_t used;
    IGRAPH_ASSERT(igraph_vector_int_list_size(memberships) == n);
    igraph_vector_bool_init(&used, nb_clusters);
    for (igraph_int_t v = 0; v < n; v++) {
        const igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_int_t k = igraph_vector_int_size(row);
        IGRAPH_ASSERT(k >= 1 && k <= max_memberships);
        for (igraph_int_t i = 0; i < k; i++) {
            IGRAPH_ASSERT(VECTOR(*row)[i] >= 0 && VECTOR(*row)[i] < nb_clusters);
            IGRAPH_ASSERT(i == 0 || VECTOR(*row)[i - 1] < VECTOR(*row)[i]);
            VECTOR(used)[VECTOR(*row)[i]] = true;
        }
    }
    for (igraph_int_t c = 0; c < nb_clusters; c++) {
        IGRAPH_ASSERT(VECTOR(used)[c]);
    }
    igraph_vector_bool_destroy(&used);
}

/* K_8 with unit weights and gamma = 1 has zero pair values, so the unit-l2
 * potential is constant. The multilevel phase runs the disjoint mover on a
 * token graph with weights 1/sqrt(k_u k_v); with strict floating-point
 * comparisons, rounding noise made that mover cycle forever for about half
 * of the seeds of this warm start. */
static void test_zero_potential_token_stage_terminates(void) {
    const int rows[8][6] = {
        {4, -1}, {0, 2, 3, 4, 5, -1}, {3, -1}, {5, -1}, {0, 1, 2, 3, 4, 5},
        {0, 2, 3, 5, -1}, {1, 2, 4, 5, -1}, {0, 1, 2, 3, 4, 5}
    };
    igraph_t graph;

    igraph_full(&graph, 8, IGRAPH_UNDIRECTED, IGRAPH_NO_LOOPS);
    for (igraph_int_t seed = 0; seed < 10; seed++) {
        igraph_vector_int_list_t memberships;
        igraph_int_t nb_clusters;
        igraph_real_t quality;
        igraph_vector_int_list_init(&memberships, 8);
        for (int v = 0; v < 8; v++) {
            for (int i = 0; i < 6 && rows[v][i] >= 0; i++) {
                igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&memberships, v),
                                            rows[v][i]);
            }
        }
        igraph_rng_seed(igraph_rng_default(), seed);
        IGRAPH_ASSERT(igraph_community_leiden(&graph, NULL, NULL, NULL, 1.0, 0.1, 8, true, -1,
                      true, false, NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
        assert_valid_cover(&memberships, 8, 8, nb_clusters);
        /* The potential is constant: -gamma/2 * sum_v w_v^2 / W = -4/28. */
        IGRAPH_ASSERT(fabs(quality + 4.0 / 28.0) < 1e-12);
        igraph_vector_int_list_destroy(&memberships);
    }
    igraph_destroy(&graph);
    printf("Zero-potential token stage terminates: OK\n");
}

/* Disjoint path, signed edge weights, zero resolution, isolation disabled:
 * vertex 0 sits with vertex 1 across a -1 edge. Every other community has
 * gain 0 > -1, so a best response must leave; the omitted-community
 * completion has to offer one although all omitted gains are zero. */
static void test_disjoint_zero_resolution_signed_witness(void) {
    igraph_t graph;
    igraph_vector_t weights;
    igraph_vector_int_t membership;
    igraph_int_t nb;
    igraph_real_t quality;

    igraph_small(&graph, 4, IGRAPH_UNDIRECTED, 0, 1, 2, 3, -1);
    igraph_vector_init(&weights, 2);
    VECTOR(weights)[0] = -1.0;
    VECTOR(weights)[1] = 2.0;
    igraph_vector_int_init(&membership, 4);
    VECTOR(membership)[0] = 0; VECTOR(membership)[1] = 0;
    VECTOR(membership)[2] = 1; VECTOR(membership)[3] = 1;
    igraph_rng_seed(igraph_rng_default(), 1);
    IGRAPH_ASSERT(igraph_community_leiden(&graph, &weights, NULL, NULL, 0.0, 0.01, 1, true, -1,
                  false, true, &membership, NULL, &nb, &quality) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(VECTOR(membership)[0] != VECTOR(membership)[1]);
    IGRAPH_ASSERT(VECTOR(membership)[2] == VECTOR(membership)[3]);
    igraph_vector_int_destroy(&membership);
    igraph_vector_destroy(&weights);
    igraph_destroy(&graph);
    printf("Disjoint zero-resolution signed witness: OK\n");
}

/* Signed node weights can make an omitted occupied cluster better than an
 * empty cluster, even at positive resolution with isolation enabled. Vertex
 * 0 is isolated, but gains 1 (undirected) or 2 (directed) by joining {1, 2}.
 * The edge of weight 100 keeps those two vertices together for every visit
 * order. Cover undirected masses, shared directed in/out weights, and a
 * negative weight in only one directed vector. */
static void test_disjoint_signed_node_weight_witness(void) {
    const igraph_real_t signed_both[] = {1.0, -2.0, 1.0};
    const igraph_real_t signed_one[] = {1.0, -5.0, 1.0};
    const igraph_real_t positive[] = {1.0, 1.0, 1.0};
    const igraph_real_t edge_value[] = {100.0};
    const igraph_vector_t weights = igraph_vector_view(edge_value, 1);
    const igraph_vector_t both = igraph_vector_view(signed_both, 3);
    const igraph_vector_t one = igraph_vector_view(signed_one, 3);
    const igraph_vector_t nonnegative = igraph_vector_view(positive, 3);

    for (igraph_int_t mode = 0; mode < 4; mode++) {
        igraph_t graph;
        igraph_vector_int_t membership;
        const igraph_vector_t *out = mode < 2 ? &both :
                                            mode == 2 ? &nonnegative : &one;
        const igraph_vector_t *in = mode < 2 ? NULL :
                                           mode == 2 ? &one : &nonnegative;

        igraph_small(&graph, 3, mode != 0, 1, 2, -1);
        igraph_vector_int_init(&membership, 3);
        for (igraph_int_t seed = 0; seed < 4; seed++) {
            igraph_int_t nb;
            VECTOR(membership)[0] = 0;
            VECTOR(membership)[1] = VECTOR(membership)[2] = 1;
            igraph_rng_seed(igraph_rng_default(), seed);
            IGRAPH_ASSERT(igraph_community_leiden(
                &graph, &weights, out, in, 1.0, 0.01, 1, true, -1,
                true, true, &membership, NULL, &nb, NULL) == IGRAPH_SUCCESS);
            IGRAPH_ASSERT(nb == 1);
            IGRAPH_ASSERT(VECTOR(membership)[0] == VECTOR(membership)[1]);
            IGRAPH_ASSERT(VECTOR(membership)[1] == VECTOR(membership)[2]);
        }
        igraph_vector_int_destroy(&membership);
        igraph_destroy(&graph);
    }
    printf("Disjoint signed-node-weight omitted cluster: OK\n");
}

/* Vertex 0 alone holds labels 0 and 1. Their true gains are exactly zero,
 * but subtracting then adding its large self penalty used to leave a
 * positive rounding residual in its current score. Under exact K=3, the
 * best response retains those labels and also joins label 2: its utility
 * increases from zero to 1/sqrt(3). The edge of weight 100 keeps vertices
 * 1 and 2 in label 2. Computing utility directly from the other rows avoids
 * the cancellation that caused the defect. */
static void test_exclusive_label_current_score_is_zero(void) {
    const igraph_real_t edge_values[] = {1.0, 100.0};
    const igraph_real_t node_values[] = {1e8, 0.0, 0.0};
    const igraph_vector_t weights = igraph_vector_view(edge_values, 2);
    const igraph_vector_t node_weights = igraph_vector_view(node_values, 3);
    igraph_t graph;
    igraph_vector_int_list_t rows;

    igraph_small(&graph, 3, IGRAPH_UNDIRECTED, 0, 1, 1, 2, -1);
    igraph_vector_int_list_init(&rows, 3);
    for (igraph_int_t seed = 0; seed < 4; seed++) {
        igraph_int_t nb;
        igraph_real_t direct_utility;
        for (igraph_int_t v = 0; v < 3; v++) {
            igraph_vector_int_clear(igraph_vector_int_list_get_ptr(&rows, v));
        }
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&rows, 0), 0);
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&rows, 0), 1);
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&rows, 1), 2);
        igraph_vector_int_push_back(igraph_vector_int_list_get_ptr(&rows, 2), 2);
        igraph_rng_seed(igraph_rng_default(), seed);
        IGRAPH_ASSERT(igraph_community_leiden_with_constraints(
            &graph, &weights, &node_weights, NULL, 1.0, 0.01, 3, -1, 3,
            true, -1, true, true, NULL, &rows, &nb, NULL) == IGRAPH_SUCCESS);
        IGRAPH_ASSERT(nb == 3);
        IGRAPH_ASSERT(igraph_vector_int_size(igraph_vector_int_list_get_ptr(&rows, 0)) == 3);
        IGRAPH_ASSERT(igraph_vector_int_size(igraph_vector_int_list_get_ptr(&rows, 1)) == 1);
        IGRAPH_ASSERT(igraph_vector_int_size(igraph_vector_int_list_get_ptr(&rows, 2)) == 1);
        IGRAPH_ASSERT(igraph_vector_int_all_e(igraph_vector_int_list_get_ptr(&rows, 1),
                                               igraph_vector_int_list_get_ptr(&rows, 2)));
        direct_utility = igraph_vector_int_contains(
            igraph_vector_int_list_get_ptr(&rows, 0),
            VECTOR(*igraph_vector_int_list_get_ptr(&rows, 1))[0]) / sqrt(3.0);
        IGRAPH_ASSERT(fabs(direct_utility - 1.0 / sqrt(3.0)) < 1e-15);
        IGRAPH_ASSERT(direct_utility > 0.5); /* the starting utility was zero */
    }
    igraph_vector_int_list_destroy(&rows);
    igraph_destroy(&graph);
    printf("Exclusive-label current score avoids self cancellation: OK\n");
}

/* The diagnostic entry point recomputes every accepted move and the token
 * identity from scratch. Those recomputations sum O(m + #labels) terms, so
 * comparing them with a purely relative margin reported false mismatches on
 * most seeds of the karate club. */
static void test_diagnostic_checks_have_no_false_mismatch(void) {
    igraph_t graph;

    igraph_famous(&graph, "Zachary");
    for (igraph_int_t seed = 0; seed < 50; seed++) {
        igraph_vector_int_list_t memberships;
        igraph_matrix_t moves, projections;
        igraph_int_t nb_clusters;
        igraph_real_t quality;
        igraph_vector_int_list_init(&memberships, 0);
        igraph_rng_seed(igraph_rng_default(), seed);
        IGRAPH_ASSERT(igraph_community_leiden_with_diagnostics(
            &graph, NULL, NULL, NULL, 0.1, 0.01, 2, false, -1, true, false,
            &memberships, &nb_clusters, &quality, &moves, &projections) == IGRAPH_SUCCESS);
        IGRAPH_ASSERT(igraph_matrix_nrow(&moves) > 0);
        for (igraph_int_t row = 0; row < igraph_matrix_nrow(&moves); row++) {
            IGRAPH_ASSERT(MATRIX(moves, row, IGRAPH_LEIDEN_OVERLAP_MOVE_ABS_ERROR) <=
                          MATRIX(moves, row, IGRAPH_LEIDEN_OVERLAP_MOVE_TOLERANCE));
            /* The margin stays far below any genuine bookkeeping error. */
            IGRAPH_ASSERT(MATRIX(moves, row, IGRAPH_LEIDEN_OVERLAP_MOVE_TOLERANCE) < 1e-9);
        }
        igraph_matrix_destroy(&projections);
        igraph_matrix_destroy(&moves);
        igraph_vector_int_list_destroy(&memberships);
    }
    igraph_destroy(&graph);
    printf("Diagnostic checks have no false mismatch: OK\n");
}

/* Disjoint CPM with signed edge weights, found by the build-to-build
 * equivalence harness: the last aggregation level's local moving splits
 * clusters of aggregate vertices. Earlier releases did not write that level
 * back to the original vertices, so every iteration reported a change and a
 * negative iteration budget never returned. The result must also pass the
 * local-moving certificate. */
static void test_disjoint_last_level_is_projected(void) {
    const igraph_int_t e[] = {6, 1, 14, 1, 16, 1, 17, 2, 8, 3, 17, 3, 6, 4, 14, 4, 13, 5,
                              19, 5, 7, 6, 16, 6, 19, 6, 8, 7, 13, 7, 19, 7, 18, 9, 21, 10,
                              13, 11, 15, 14, 21, 14, 20, 15, 19, 18};
    const igraph_real_t w[] = {0.87250426563667516, 0.87856437614189753, -0.60782966326309407,
                               0.17863898651767429, 1.5366411770996138, -0.98872577562274611,
                               1.36593910808448, 1.174959849113645, -0.054382351986993593,
                               1.9706319952132403, 1.8531563597325611, 1.2780643362987743,
                               -0.41017175803095896, 1.0293519484260891, -0.35159892998302511,
                               -0.053375278740130816, 1.0656015505516214, 1.7267650321968193,
                               1.6004706218026841, 1.3445501913036373, -0.37438692971097853,
                               0.75772998784286083, -0.72160485044115674};
    const igraph_int_t start[] = {1, 18, 6, 19, 11, 21, 12, 16, 9, 5, 2, 16, 8, 14, 21, 11,
                                  20, 13, 4, 9, 21, 14};
    const igraph_vector_int_t edges = igraph_vector_int_view(e, 46);
    const igraph_vector_t weights = igraph_vector_view(w, 23);
    igraph_t graph;
    igraph_vector_int_t membership, certified;
    igraph_int_t nb;
    igraph_real_t quality, quality_after;

    igraph_create(&graph, &edges, 22, IGRAPH_UNDIRECTED);
    igraph_vector_int_init_array(&membership, start, 22);
    igraph_rng_seed(igraph_rng_default(), 1272836011);
    IGRAPH_ASSERT(igraph_community_leiden_simple(&graph, &weights, IGRAPH_LEIDEN_OBJECTIVE_CPM,
                  0.29295743626135579, 0.001, true, -1, &membership, &nb,
                  &quality) == IGRAPH_SUCCESS);

    /* No vertex can improve by a local move (Nash certificate). */
    igraph_vector_int_init_copy(&certified, &membership);
    IGRAPH_ASSERT(igraph_community_leiden(&graph, &weights, NULL, NULL, 0.29295743626135579,
                  0.001, 1, true, 1, true, true, &certified, NULL, NULL,
                  &quality_after) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(igraph_vector_int_all_e(&membership, &certified));
    IGRAPH_ASSERT(quality_after == quality);

    igraph_vector_int_destroy(&certified);
    igraph_vector_int_destroy(&membership);
    igraph_destroy(&graph);
    printf("Disjoint last aggregation level is projected: OK\n");
}

static igraph_int_t count_duplicate_bodies(const igraph_vector_int_list_t *memberships,
                                           igraph_int_t nb_clusters) {
    const igraph_int_t n = igraph_vector_int_list_size(memberships);
    igraph_int_t duplicates = 0;

    for (igraph_int_t a = 0; a < nb_clusters; a++) {
        for (igraph_int_t b = a + 1; b < nb_clusters; b++) {
            igraph_bool_t same = true;
            for (igraph_int_t v = 0; v < n && same; v++) {
                const igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(memberships, v);
                same = igraph_vector_int_contains(row, a) == igraph_vector_int_contains(row, b);
            }
            duplicates += same;
        }
    }
    return duplicates;
}

/* Star 1-0-2 at zero resolution with two labels per vertex: local moving can
 * reach a cover in which every vertex holds the same two labels. The token
 * proposal merges them into one label with the same potential (a tie within
 * the margin), which single-vertex moves cannot do. The post-local guard
 * must keep such a tied proposal when it occupies fewer labels, and must
 * never return less than local moving alone. */
static void test_tied_token_proposal_merges_duplicate_labels(void) {
    igraph_t graph;
    igraph_int_t exercised = 0;

    igraph_small(&graph, 3, IGRAPH_UNDIRECTED, 0, 1, 0, 2, -1);
    for (igraph_int_t seed = 0; seed < 20; seed++) {
        igraph_vector_int_list_t local, full;
        igraph_int_t nb_local, nb_full;
        igraph_real_t q_local, q_full;

        igraph_vector_int_list_init(&local, 0);
        igraph_vector_int_list_init(&full, 0);
        igraph_rng_seed(igraph_rng_default(), seed);
        IGRAPH_ASSERT(igraph_community_leiden(&graph, NULL, NULL, NULL, 0.0, 0.01, 2, false, 1,
                      true, true, NULL, &local, &nb_local, &q_local) == IGRAPH_SUCCESS);
        igraph_rng_seed(igraph_rng_default(), seed);
        IGRAPH_ASSERT(igraph_community_leiden(&graph, NULL, NULL, NULL, 0.0, 0.01, 2, false, 2,
                      true, false, NULL, &full, &nb_full, &q_full) == IGRAPH_SUCCESS);
        assert_valid_cover(&full, 3, 2, nb_full);
        IGRAPH_ASSERT(q_full >= q_local - 1e-12);
        if (count_duplicate_bodies(&local, nb_local) > 0) {
            exercised++;
            IGRAPH_ASSERT(count_duplicate_bodies(&full, nb_full) == 0);
            IGRAPH_ASSERT(nb_full < nb_local);
        }
        igraph_vector_int_list_destroy(&full);
        igraph_vector_int_list_destroy(&local);
    }
    IGRAPH_ASSERT(exercised > 0);
    igraph_destroy(&graph);
    printf("Tied token proposal merges duplicate labels: OK\n");
}

int main(void) {
    const igraph_real_t resolutions[] = { -0.4, -0.05, 0.0, 0.02, 0.1, 0.35, 1.0 };
    const igraph_int_t n_resolutions = sizeof(resolutions) / sizeof(resolutions[0]);
    igraph_int_t audited = 0, runs = 0;
    igraph_real_t worst = 0.0;

    test_zero_potential_token_stage_terminates();
    test_disjoint_zero_resolution_signed_witness();
    test_disjoint_signed_node_weight_witness();
    test_exclusive_label_current_score_is_zero();
    test_diagnostic_checks_have_no_false_mismatch();
    test_tied_token_proposal_merges_duplicate_labels();
    test_disjoint_last_level_is_projected();

    igraph_rng_seed(igraph_rng_default(), 20260927);

    for (igraph_int_t trial = 0; trial < 600; trial++) {
        igraph_t graph;
        igraph_vector_t edge_weights, node_weights;
        igraph_vector_int_list_t memberships;
        const igraph_int_t n = RNG_INTEGER(3, 60);
        const igraph_real_t p = RNG_UNIF(0.03, 0.4);
        const igraph_real_t gamma = resolutions[RNG_INTEGER(0, n_resolutions - 1)];
        const igraph_bool_t allow_isolation = RNG_BOOL();
        const igraph_bool_t local_move_only = RNG_INTEGER(0, 3) != 0;
        const igraph_bool_t weighted = RNG_INTEGER(0, 2) == 0;
        const igraph_bool_t node_weighted = RNG_INTEGER(0, 2) == 0;
        const igraph_bool_t warm = RNG_BOOL();
        const igraph_int_t n_iterations = RNG_INTEGER(0, 4) == 0 ? 2 : -1;
        igraph_int_t max_memberships, nb_clusters;
        igraph_real_t quality;

        igraph_erdos_renyi_game_gnp(&graph, n, p, IGRAPH_UNDIRECTED, IGRAPH_SIMPLE_SW, false);
        if (igraph_ecount(&graph) == 0) {
            igraph_add_edge(&graph, 0, 1);
        }
        /* Include the disjoint path (M = 1), which shares the omitted-label
         * completion through the cluster index. */
        max_memberships = RNG_INTEGER(0, 4) == 0 ? 1 :
                          RNG_INTEGER(0, 3) == 0 ? n : RNG_INTEGER(2, 5);
        if (max_memberships > n) {
            max_memberships = n;
        }

        igraph_vector_init(&edge_weights, igraph_ecount(&graph));
        for (igraph_int_t e = 0; e < igraph_ecount(&graph); e++) {
            VECTOR(edge_weights)[e] = weighted ? RNG_UNIF(0.2, 3.0) : 1.0;
        }
        igraph_vector_init(&node_weights, n);
        for (igraph_int_t v = 0; v < n; v++) {
            /* Include zero node weights, which remove a vertex from crowding. */
            VECTOR(node_weights)[v] = node_weighted ? (igraph_real_t) RNG_INTEGER(0, 3) : 1.0;
        }

        igraph_vector_int_list_init(&memberships, n);
        if (warm) {
            const igraph_int_t labels = RNG_INTEGER(1, n);
            for (igraph_int_t v = 0; v < n; v++) {
                igraph_vector_int_t *row = igraph_vector_int_list_get_ptr(&memberships, v);
                const igraph_int_t k = RNG_INTEGER(1, max_memberships < labels ? max_memberships : labels);
                for (igraph_int_t i = 0; i < k; i++) {
                    igraph_int_t c = RNG_INTEGER(0, labels - 1);
                    if (!igraph_vector_int_contains(row, c)) {
                        igraph_vector_int_push_back(row, c);
                    }
                }
            }
        }

        IGRAPH_ASSERT(igraph_community_leiden(
            &graph, &edge_weights, &node_weights, NULL, gamma, 0.01,
            max_memberships, warm, n_iterations, allow_isolation, local_move_only,
            NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
        runs++;
        assert_valid_cover(&memberships, n, max_memberships, nb_clusters);

        if (n_iterations < 0) {
            const igraph_real_t regret = max_relative_regret(
                &graph, &edge_weights, &node_weights, gamma, max_memberships,
                allow_isolation, &memberships);
            if (regret > worst) {
                worst = regret;
            }
            if (regret > 1e-9) {
                printf("trial %" IGRAPH_PRId ": relative regret %g (n=%" IGRAPH_PRId
                       ", gamma=%g, M=%" IGRAPH_PRId ", iso=%d, local=%d)\n",
                       trial, regret, n, gamma, max_memberships,
                       (int) allow_isolation, (int) local_move_only);
                IGRAPH_FATAL("Returned cover is not a bounded best response.");
            }
            audited++;
        }

        igraph_vector_int_list_destroy(&memberships);
        igraph_vector_destroy(&node_weights);
        igraph_vector_destroy(&edge_weights);
        igraph_destroy(&graph);
    }

    IGRAPH_ASSERT(runs == 600);
    IGRAPH_ASSERT(audited > 400);
    printf("Overlapping Leiden randomized certificate audit: OK\n");

    VERIFY_FINALLY_STACK();
    return 0;
}

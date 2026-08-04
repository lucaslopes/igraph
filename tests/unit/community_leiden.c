/*
   igraph library.
   Copyright (C) 2006-2012  Gabor Csardi <csardi.gabor@gmail.com>
   334 Harvard street, Cambridge, MA 02139 USA

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc.,  51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301 USA

*/

#include <igraph.h>

#include "test_utilities.h"

/* Unified public API: max_memberships=1 is disjoint, >1 is overlapping. */
#define TOL (1e-15)

void run_leiden_CPM(const igraph_t *graph, const igraph_vector_t *edge_weights, const igraph_real_t resolution) {

    igraph_vector_int_t membership;
    igraph_int_t nb_clusters = igraph_vcount(graph);
    igraph_real_t quality, quality2;

    /* Initialize with singleton partition. */
    igraph_vector_int_init(&membership, igraph_vcount(graph));

    /* Use same seed as for the simplified interface below, to ensure the same result. */
    igraph_rng_seed(igraph_rng_default(), 123);
    igraph_community_leiden(graph, edge_weights, NULL, NULL, resolution, 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*local_move_only=*/ 0,
                            &membership, /*memberships=*/ NULL, &nb_clusters, &quality);

    /* Handle negative zeros. */
    if (fabs(quality) < TOL) quality = 0.0;

    printf("Leiden found %" IGRAPH_PRId " clusters using CPM (resolution parameter=%.2f), quality is %.5f.\n", nb_clusters, resolution, quality);

    printf("Membership: ");
    igraph_vector_int_print(&membership);
    printf("\n");

    quality2 = quality;

    /* Use same seed as for the generic interface above, to ensure the same result. */
    igraph_rng_seed(igraph_rng_default(), 123);
    igraph_community_leiden_simple(graph,
                                   edge_weights,
                                   IGRAPH_LEIDEN_OBJECTIVE_CPM,
                                   resolution, 0.01, false, 2, &membership,
                                   NULL,
                                   &quality);
    if (fabs(quality) < TOL) quality = 0.0;
    IGRAPH_ASSERT((isnan(quality) && isnan(quality2)) ||
                  igraph_almost_equals(quality, quality2, TOL));

    igraph_vector_int_destroy(&membership);
}

void run_leiden_modularity(igraph_t *graph, igraph_vector_t *edge_weights) {

    const igraph_bool_t directed = igraph_is_directed(graph);
    igraph_vector_int_t membership;
    igraph_vector_t out_strength, in_strength;
    igraph_int_t nb_clusters = igraph_vcount(graph);
    igraph_real_t quality, quality2;
    const igraph_real_t directed_multiplier = directed ? 1.0 : 2.0;
    igraph_real_t m;

    igraph_vector_init(&out_strength, igraph_vcount(graph));
    igraph_strength(graph, &out_strength, igraph_vss_all(), IGRAPH_OUT, IGRAPH_LOOPS, edge_weights);

    if (directed) {
        igraph_vector_init(&in_strength, igraph_vcount(graph));
        igraph_strength(graph, &in_strength, igraph_vss_all(), IGRAPH_IN, IGRAPH_LOOPS, edge_weights);
    }

    m = edge_weights ? igraph_vector_sum(edge_weights) : igraph_ecount(graph);

    /* Initialize with singleton partition. */
    igraph_vector_int_init(&membership, igraph_vcount(graph));

    /* Use same seed as for the simplified interface below, to ensure the same result. */
    igraph_rng_seed(igraph_rng_default(), 123);
    igraph_community_leiden(graph, edge_weights, &out_strength, directed ? &in_strength : NULL,
                            1.0 / (directed_multiplier * m), 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*local_move_only=*/ 0,
                            &membership, /*memberships=*/ NULL, &nb_clusters, &quality);

    igraph_modularity(graph, &membership, edge_weights, 1.0, IGRAPH_DIRECTED, &quality2);
    if (isnan(quality)) {
        printf("Leiden found %" IGRAPH_PRId " clusters using modularity, %s, quality is nan.\n", nb_clusters, directed ? "directed" : "undirected");
        IGRAPH_ASSERT(isnan(quality2));
    } else {
        /* It is necessary to not only use igraph_almost_equals(), but also check
         * if the values are both very close to zero due to roundoff errors. */

        if (fabs(quality) < TOL) quality = 0.0;
        if (fabs(quality2) < TOL) quality2 = 0.0;

        printf("Leiden found %" IGRAPH_PRId " clusters using modularity, %s, quality is %.5f.\n", nb_clusters, directed ? "directed" : "undirected", quality);
        IGRAPH_ASSERT(igraph_almost_equals(quality, quality2, TOL));
    }

    printf("Membership: ");
    igraph_vector_int_print(&membership);
    printf("\n");

    /* Use same seed as for the generic interface above, to ensure the same result. */
    igraph_rng_seed(igraph_rng_default(), 123);
    igraph_community_leiden_simple(graph,
                                   edge_weights,
                                   IGRAPH_LEIDEN_OBJECTIVE_MODULARITY,
                                   1.0, 0.01, false, 2, &membership, NULL, &quality);
    if (fabs(quality) < TOL) quality = 0.0;
    IGRAPH_ASSERT((isnan(quality) && isnan(quality2)) ||
                  igraph_almost_equals(quality, quality2, TOL));

    igraph_vector_int_destroy(&membership);
    if (directed) igraph_vector_destroy(&in_strength);
    igraph_vector_destroy(&out_strength);
}

void run_leiden_overlapping(const igraph_t *graph, const igraph_vector_t *edge_weights,
                             const igraph_real_t resolution_parameter,
                             const igraph_integer_t max_memberships) {

    igraph_vector_int_list_t memberships;
    igraph_integer_t nb_clusters;
    igraph_real_t quality;

    igraph_vector_int_list_init(&memberships, 0);

    igraph_community_leiden(graph, edge_weights, NULL, NULL, resolution_parameter,
                            0.01, max_memberships, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*local_move_only=*/ 0,
                            /*membership=*/ NULL, &memberships, &nb_clusters, &quality);

    printf("Overlapping Leiden found %" IGRAPH_PRId " clusters using CPM (resolution parameter=%.2f, max memberships=%" IGRAPH_PRId "), quality is %.4f.\n",
           nb_clusters, resolution_parameter, max_memberships, quality);

    printf("Memberships: ");
    print_vector_int_list(&memberships);
    printf("\n");

    igraph_vector_int_list_destroy(&memberships);
}

/* Regression: max_memberships == 1 must follow the disjoint result path.
 * The flat membership form and the memberships-list form must yield the
 * same partition and quality under the same seed, proving both use the
 * disjoint driver, not the overlapping token-graph path. */
void test_max_memberships_one_is_disjoint(void) {
    igraph_t graph;
    igraph_vector_int_t membership;
    igraph_vector_int_list_t memberships;
    igraph_integer_t nb_a, nb_b;
    igraph_real_t quality_a, quality_b;
    igraph_integer_t i, n;

    /* Two cliques joined by a bridge — same small graph as other CPM tests. */
    igraph_small(&graph, 10, IGRAPH_UNDIRECTED,
                 0, 1, 0, 2, 0, 3, 0, 4, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4, 3, 4,
                 5, 6, 5, 7, 5, 8, 5, 9, 6, 7, 6, 8, 6, 9, 7, 8, 7, 9, 8, 9,
                 0, 5, -1);
    n = igraph_vcount(&graph);

    igraph_vector_int_init(&membership, n);
    igraph_vector_int_list_init(&memberships, 0);

    /* Explicit disjoint call: max_memberships=1, membership vector. */
    igraph_rng_seed(igraph_rng_default(), 42);
    igraph_community_leiden(&graph, NULL, NULL, NULL, 0.05, 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*local_move_only=*/ 0,
                            &membership, /*memberships=*/ NULL, &nb_a, &quality_a);

    /* Same parameters via memberships-only (list form). */
    igraph_rng_seed(igraph_rng_default(), 42);
    igraph_community_leiden(&graph, NULL, NULL, NULL, 0.05, 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*local_move_only=*/ 0,
                            /*membership=*/ NULL, &memberships, &nb_b, &quality_b);

    IGRAPH_ASSERT(nb_a == nb_b);
    IGRAPH_ASSERT(quality_a == quality_b);
    IGRAPH_ASSERT(igraph_vector_int_size(&membership) == n);
    IGRAPH_ASSERT(igraph_vector_int_list_size(&memberships) == n);
    for (i = 0; i < n; i++) {
        const igraph_vector_int_t *sigma =
            igraph_vector_int_list_get_ptr(&memberships, i);
        IGRAPH_ASSERT(igraph_vector_int_size(sigma) == 1);
        IGRAPH_ASSERT(VECTOR(*sigma)[0] == VECTOR(membership)[i]);
    }

    /* Missing both outputs in disjoint mode is an error. */
    CHECK_ERROR(
        igraph_community_leiden(&graph, NULL, NULL, NULL, 0.05, 0.01,
                                1, 0, 2, 1, 0,
                                /*membership=*/ NULL, /*memberships=*/ NULL,
                                &nb_a, &quality_a),
        IGRAPH_EINVAL);

    igraph_vector_int_destroy(&membership);
    igraph_vector_int_list_destroy(&memberships);
    igraph_destroy(&graph);

    printf("max_memberships=1 disjoint-path regression: OK\n\n");
}

static void assert_overlapping_cover_valid(const igraph_vector_int_list_t *memberships,
                                           const igraph_integer_t n,
                                           const igraph_integer_t max_memberships) {
    IGRAPH_ASSERT(igraph_vector_int_list_size(memberships) == n);
    for (igraph_integer_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma =
            igraph_vector_int_list_get_ptr(memberships, v);
        const igraph_integer_t k = igraph_vector_int_size(sigma);

        IGRAPH_ASSERT(k >= 1 && k <= max_memberships);
        for (igraph_integer_t i = 0; i < k; i++) {
            IGRAPH_ASSERT(VECTOR(*sigma)[i] >= 0);
            if (i > 0) {
                IGRAPH_ASSERT(VECTOR(*sigma)[i - 1] < VECTOR(*sigma)[i]);
            }
        }
    }
}

static void assert_overlapping_covers_equal(const igraph_vector_int_list_t *a,
                                            const igraph_vector_int_list_t *b) {
    const igraph_integer_t n = igraph_vector_int_list_size(a);

    IGRAPH_ASSERT(igraph_vector_int_list_size(b) == n);
    for (igraph_integer_t v = 0; v < n; v++) {
        const igraph_vector_int_t *sigma_a =
            igraph_vector_int_list_get_ptr(a, v);
        const igraph_vector_int_t *sigma_b =
            igraph_vector_int_list_get_ptr(b, v);
        const igraph_integer_t k = igraph_vector_int_size(sigma_a);

        IGRAPH_ASSERT(igraph_vector_int_size(sigma_b) == k);
        for (igraph_integer_t i = 0; i < k; i++) {
            IGRAPH_ASSERT(VECTOR(*sigma_a)[i] == VECTOR(*sigma_b)[i]);
        }
    }
}

static void make_native_nontermination_fixture(igraph_t *graph) {
    static const igraph_int_t edge_data[] = {
        0, 9, 0, 23, 0, 30, 0, 62, 1, 31, 1, 49, 1, 60, 1, 77,
        2, 10, 2, 18, 2, 26, 2, 27, 2, 28, 2, 35, 2, 40, 2, 45,
        2, 53, 2, 71, 2, 79, 3, 4, 3, 60, 3, 62, 4, 8, 4, 42,
        4, 70, 5, 27, 5, 32, 5, 35, 5, 63, 5, 68, 5, 70, 6, 7,
        6, 10, 6, 36, 7, 16, 7, 21, 7, 36, 7, 50, 7, 51, 8, 20,
        8, 35, 8, 37, 8, 43, 8, 62, 8, 75, 9, 16, 9, 29, 9, 41,
        9, 44, 9, 58, 9, 66, 10, 12, 10, 27, 10, 28, 10, 31, 10, 35,
        10, 70, 10, 71, 10, 72, 10, 78, 11, 55, 11, 63, 12, 27,
        12, 32, 12, 35, 12, 37, 12, 41, 12, 70, 13, 14, 13, 30,
        13, 54, 14, 17, 14, 26, 14, 29, 14, 69, 15, 18, 15, 22,
        15, 52, 15, 64, 15, 74, 15, 77, 16, 31, 16, 42, 16, 69,
        16, 72, 17, 39, 17, 51, 17, 69, 18, 41, 19, 30, 19, 44,
        20, 21, 20, 24, 20, 47, 20, 77, 21, 59, 22, 31, 22, 43,
        22, 47, 22, 67, 23, 51, 23, 60, 23, 63, 24, 28, 24, 52,
        24, 61, 24, 66, 24, 73, 25, 38, 25, 40, 25, 42, 25, 52,
        25, 55, 25, 67, 25, 77, 27, 56, 28, 35, 28, 52, 28, 78,
        29, 30, 30, 33, 30, 54, 32, 45, 32, 54, 32, 67, 33, 45,
        33, 77, 34, 35, 34, 58, 35, 39, 35, 40, 35, 53, 35, 55,
        35, 57, 35, 70, 35, 71, 35, 72, 35, 75, 35, 79, 38, 42,
        38, 43, 39, 43, 39, 61, 41, 43, 42, 67, 43, 48, 43, 56,
        43, 64, 43, 68, 43, 77, 44, 55, 45, 79, 46, 50, 46, 61,
        46, 77, 46, 79, 47, 74, 48, 53, 48, 57, 49, 76, 50, 56,
        50, 59, 51, 65, 53, 55, 55, 62, 55, 68, 56, 74, 57, 73,
        63, 73, 65, 71, 66, 71, 67, 77, 75, 76
    };
    igraph_vector_int_t edges;

    IGRAPH_ASSERT(igraph_vector_int_init(&edges,
                                         (igraph_integer_t) (sizeof(edge_data) /
                                                              sizeof(edge_data[0]))) == IGRAPH_SUCCESS);
    for (igraph_integer_t i = 0; i < igraph_vector_int_size(&edges); i++) {
        VECTOR(edges)[i] = edge_data[i];
    }
    IGRAPH_ASSERT(igraph_create(graph, &edges, 80, IGRAPH_UNDIRECTED) == IGRAPH_SUCCESS);
    igraph_vector_int_destroy(&edges);
}

static void set_ground_truth_primary_cover(igraph_vector_int_list_t *memberships) {
    static const igraph_int_t primary[80] = {
        0, 0, 1, 0, 1, 1, 2, 2, 1, 0, 1, 0, 1, 2, 2, 3,
        0, 2, 3, 0, 3, 2, 3, 0, 0, 1, 2, 1, 1, 2, 0, 0,
        1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 3, 3, 0, 1, 2, 3,
        1, 3, 2, 2, 1, 1, 2, 0, 2, 0, 2, 2, 0, 0, 0, 0,
        3, 2, 2, 3, 3, 0, 1, 1, 1, 0, 3, 1, 1, 3, 1, 1
    };

    IGRAPH_ASSERT(igraph_vector_int_list_resize(memberships, 80) == IGRAPH_SUCCESS);
    for (igraph_integer_t v = 0; v < 80; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        IGRAPH_ASSERT(igraph_vector_int_resize(sigma, 1) == IGRAPH_SUCCESS);
        VECTOR(*sigma)[0] = primary[v];
    }
}

static void test_native_nontermination_fixture(void) {
    igraph_t graph;
    igraph_vector_int_list_t memberships, snapshot;
    igraph_vector_int_t membership;
    igraph_integer_t nb_clusters;
    igraph_real_t density, quality, snapshot_quality;

    make_native_nontermination_fixture(&graph);
    IGRAPH_ASSERT(igraph_density(&graph, NULL, &density, false) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(igraph_vector_int_list_init(&memberships, 0) == IGRAPH_SUCCESS);

    /* n_iterations=0 performs no overlapping phase and preserves singletons. */
    igraph_rng_seed(igraph_rng_default(), 0);
    IGRAPH_ASSERT(igraph_community_leiden(
        &graph, NULL, NULL, NULL, density, 0.01, 2, false, 0, true, true,
        NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
    assert_overlapping_cover_valid(&memberships, 80, 2);
    for (igraph_integer_t v = 0; v < 80; v++) {
        const igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(&memberships, v);
        IGRAPH_ASSERT(igraph_vector_int_size(sigma) == 1);
        IGRAPH_ASSERT(VECTOR(*sigma)[0] == v);
    }
    IGRAPH_ASSERT(isfinite(quality));

    /* A positive bound is honored in local-move-only mode: one phase returns. */
    igraph_vector_int_list_clear(&memberships);
    igraph_rng_seed(igraph_rng_default(), 0);
    IGRAPH_ASSERT(igraph_community_leiden(
        &graph, NULL, NULL, NULL, density, 0.01, 2, false, 1, true, true,
        NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
    assert_overlapping_cover_valid(&memberships, 80, 2);
    IGRAPH_ASSERT(isfinite(quality));

    /* Both isolation settings must terminate from the problematic singleton start. */
    igraph_vector_int_list_clear(&memberships);
    igraph_rng_seed(igraph_rng_default(), 0);
    IGRAPH_ASSERT(igraph_community_leiden(
        &graph, NULL, NULL, NULL, density, 0.01, 2, false, -1, true, true,
        NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
    assert_overlapping_cover_valid(&memberships, 80, 2);
    IGRAPH_ASSERT(isfinite(quality));

    IGRAPH_ASSERT(igraph_vector_int_list_init(&snapshot, 80) == IGRAPH_SUCCESS);
    for (igraph_integer_t v = 0; v < 80; v++) {
        IGRAPH_ASSERT(igraph_vector_int_update(
            igraph_vector_int_list_get_ptr(&snapshot, v),
            igraph_vector_int_list_get_ptr(&memberships, v)) == IGRAPH_SUCCESS);
    }
    snapshot_quality = quality;

    /* A returned cover is a stable initial cover for another negative run. */
    igraph_rng_seed(igraph_rng_default(), 0);
    IGRAPH_ASSERT(igraph_community_leiden(
        &graph, NULL, NULL, NULL, density, 0.01, 2, true, -1, true, true,
        NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
    assert_overlapping_cover_valid(&memberships, 80, 2);
    assert_overlapping_covers_equal(&memberships, &snapshot);
    IGRAPH_ASSERT(igraph_almost_equals(quality, snapshot_quality, 1e-12));

    igraph_vector_int_list_clear(&memberships);
    igraph_rng_seed(igraph_rng_default(), 0);
    IGRAPH_ASSERT(igraph_community_leiden(
        &graph, NULL, NULL, NULL, density, 0.01, 2, false, -1, false, true,
        NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
    assert_overlapping_cover_valid(&memberships, 80, 2);
    IGRAPH_ASSERT(isfinite(quality));

    /* Ground-truth-primary start is a separate cap-2 control. */
    igraph_vector_int_list_clear(&memberships);
    set_ground_truth_primary_cover(&memberships);
    igraph_rng_seed(igraph_rng_default(), 0);
    IGRAPH_ASSERT(igraph_community_leiden(
        &graph, NULL, NULL, NULL, density, 0.01, 2, true, -1, true, true,
        NULL, &memberships, &nb_clusters, &quality) == IGRAPH_SUCCESS);
    assert_overlapping_cover_valid(&memberships, 80, 2);
    IGRAPH_ASSERT(isfinite(quality));

    /* Cap 1 remains a disjoint singleton control on the same fixture. */
    IGRAPH_ASSERT(igraph_vector_int_init(&membership, 0) == IGRAPH_SUCCESS);
    igraph_rng_seed(igraph_rng_default(), 0);
    IGRAPH_ASSERT(igraph_community_leiden(
        &graph, NULL, NULL, NULL, density, 0.01, 1, false, -1, true, true,
        &membership, NULL, &nb_clusters, &quality) == IGRAPH_SUCCESS);
    IGRAPH_ASSERT(igraph_vector_int_size(&membership) == 80);
    IGRAPH_ASSERT(isfinite(quality));

    igraph_vector_int_destroy(&membership);
    igraph_vector_int_list_destroy(&snapshot);
    igraph_vector_int_list_destroy(&memberships);
    igraph_destroy(&graph);

}

int main(void) {
    igraph_t graph;
    igraph_vector_t weights;

    igraph_vector_init(&weights, 0);

    /* Set default seed to get reproducible results */
    igraph_rng_seed(igraph_rng_default(), 0);

    /* Simple unweighted graph */
    igraph_small(&graph, 10, IGRAPH_UNDIRECTED,
                 0, 1, 0, 2, 0, 3, 0, 4, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4, 3, 4,
                 5, 6, 5, 7, 5, 8, 5, 9, 6, 7, 6, 8, 6, 9, 7, 8, 7, 9, 8, 9,
                 0, 5, -1);
    run_leiden_modularity(&graph, NULL);

    /* Same simple graph, with uniform edge weights */
    igraph_vector_resize(&weights, igraph_ecount(&graph));
    igraph_vector_fill(&weights, 2);
    run_leiden_modularity(&graph, &weights);

    /* Same simple graph, but directed with reciprocal edges */
    igraph_to_directed(&graph, IGRAPH_TO_DIRECTED_MUTUAL);
    run_leiden_modularity(&graph, NULL);

    igraph_destroy(&graph);

    /* Tiny directed graph; optimal community structure is different if
     * ignoring edge directions. */
    igraph_small(&graph, 4, IGRAPH_DIRECTED, 0, 2, 0, 3, 1, 2, 3, 1, 3, 2, -1);
    run_leiden_modularity(&graph, NULL);
    igraph_to_undirected(&graph, IGRAPH_TO_UNDIRECTED_EACH, NULL);
    run_leiden_modularity(&graph, NULL);
    igraph_destroy(&graph);

    /* Larger directed graph; optimal community structure is different if
     * ignoring edge directions. */
    igraph_small(
        &graph, 10, IGRAPH_DIRECTED,
        0, 3, 0, 4, 1, 0, 1, 4, 2, 1, 3, 0, 3, 2, 4, 0, 4, 3, 4, 7, 5, 0, 5,
        1, 5, 3, 5, 6, 5, 8, 5, 9, 7, 0, 8, 2, 8, 3, 9, 1, 9, 3, 9, 8,
        -1);
    run_leiden_modularity(&graph, NULL);
    igraph_to_undirected(&graph, IGRAPH_TO_UNDIRECTED_EACH, NULL);
    run_leiden_modularity(&graph, NULL);
    igraph_destroy(&graph);

    /* Simple nonuniform weighted graph, with and without weights */
    igraph_small(&graph, 6, IGRAPH_UNDIRECTED,
                 0, 1, 1, 2, 2, 3, 2, 4, 2, 5, 3, 4, 3, 5, 4, 5, -1);
    igraph_vector_resize(&weights, 8);
    igraph_vector_fill(&weights, 1);
    VECTOR(weights)[0] = 10;
    VECTOR(weights)[1] = 10;
    run_leiden_modularity(&graph, NULL);
    run_leiden_modularity(&graph, &weights);
    igraph_destroy(&graph);

    /* Zachary Karate club */
    igraph_small(&graph, 0, IGRAPH_UNDIRECTED,
                 0,  1,  0,  2,  0,  3,  0,  4,  0,  5,
                 0,  6,  0,  7,  0,  8,  0, 10,  0, 11,
                 0, 12,  0, 13,  0, 17,  0, 19,  0, 21,
                 0, 31,  1,  2,  1,  3,  1,  7,  1, 13,
                 1, 17,  1, 19,  1, 21,  1, 30,  2,  3,
                 2,  7,  2,  8,  2,  9,  2, 13,  2, 27,
                 2, 28,  2, 32,  3,  7,  3, 12,  3, 13,
                 4,  6,  4, 10,  5,  6,  5, 10,  5, 16,
                 6, 16,  8, 30,  8, 32,  8, 33,  9, 33,
                 13, 33, 14, 32, 14, 33, 15, 32, 15, 33,
                 18, 32, 18, 33, 19, 33, 20, 32, 20, 33,
                 22, 32, 22, 33, 23, 25, 23, 27, 23, 29,
                 23, 32, 23, 33, 24, 25, 24, 27, 24, 31,
                 25, 31, 26, 29, 26, 33, 27, 33, 28, 31,
                 28, 33, 29, 32, 29, 33, 30, 32, 30, 33,
                 31, 32, 31, 33, 32, 33,
                 -1);
    run_leiden_modularity(&graph, NULL);
    run_leiden_CPM(&graph, NULL, 0.06);
    igraph_destroy(&graph);

    /* Simple disconnected graph with isolates */
    igraph_small(&graph, 9, IGRAPH_UNDIRECTED,
                 0,  1,  0,  2,  0,  3,  1,  2,  1,  3,  2,  3,
                 4,  5,  4,  6,  4,  7,  5,  6,  5,  7,  6,  7,
                 -1);
    run_leiden_modularity(&graph, NULL);
    igraph_destroy(&graph);

    /* Disjoint union of two rings */
    igraph_small(&graph, 20, IGRAPH_UNDIRECTED,
                 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 0, 9,
                 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 10, 19, -1);
    run_leiden_modularity(&graph, NULL);
    run_leiden_CPM(&graph, NULL, 0.05);
    igraph_destroy(&graph);

    /* Completely empty graph */
    igraph_small(&graph, 10, IGRAPH_UNDIRECTED, -1);
    run_leiden_modularity(&graph, NULL);
    igraph_destroy(&graph);


    /* Set default seed to get reproducible results */
    igraph_rng_seed(igraph_rng_default(), 0);

    /* Ring graph without loop edges */
    igraph_small(&graph, 6, IGRAPH_UNDIRECTED,
                 0,1, 1,2, 2,3, 3,4, 4,5, 5,0, -1);
    run_leiden_CPM(&graph, NULL, 0.4);
    igraph_destroy(&graph);

    /* Set default seed to get reproducible results */
    igraph_rng_seed(igraph_rng_default(), 0);

    /* Ring graph with loop edges */
    igraph_small(&graph, 6, IGRAPH_UNDIRECTED,
                 0,1, 1,2, 2,3, 3,4, 4,5, 5,0,
                 0,0, 1,1, 2,2, 3,3, 4,4, 5,5,
                 -1);
    run_leiden_CPM(&graph, NULL, 0.4);
    igraph_destroy(&graph);

    /* Regression test -- graph with two vertices and two edges */
    igraph_small(&graph, 2, IGRAPH_UNDIRECTED, 0, 0, 1, 1, -1);
    run_leiden_modularity(&graph, NULL);
    igraph_destroy(&graph);

    /* The next two tests need an empty weight vector. */
    igraph_vector_clear(&weights);

    /* Null graph */
    igraph_empty(&graph, 0, IGRAPH_UNDIRECTED);
    run_leiden_modularity(&graph, &weights);
    igraph_destroy(&graph);

    /* Edgeless graph */
    igraph_empty(&graph, 5, IGRAPH_UNDIRECTED);
    run_leiden_modularity(&graph, &weights);
    igraph_destroy(&graph);

    /* Check that the input is validated properly. */

    /* Small test graph. */
    igraph_small(&graph, 4, IGRAPH_UNDIRECTED,
                 0,1, 1,2, 2,0, 0,3, 3,3,
                 -1);
    igraph_vector_range(&weights, 1, igraph_ecount(&graph) + 1);

    /* Omitting membership should raise no error. */
    igraph_community_leiden_simple(&graph, &weights, IGRAPH_LEIDEN_OBJECTIVE_MODULARITY,
                                   1.0, 0.01, false, 1, NULL, NULL, NULL);

    /* Negative weight. */
    VECTOR(weights)[0] = -1;
    CHECK_ERROR(igraph_community_leiden_simple(&graph, &weights, IGRAPH_LEIDEN_OBJECTIVE_MODULARITY,
                                               1.0, 0.01, false, 1, NULL, NULL, NULL), IGRAPH_EINVAL);
    CHECK_ERROR(igraph_community_leiden_simple(&graph, &weights, IGRAPH_LEIDEN_OBJECTIVE_ER,
                                               1.0, 0.01, false, 1, NULL, NULL, NULL), IGRAPH_EINVAL);

    /* NaN weight. */
    VECTOR(weights)[0] = IGRAPH_NAN;
    CHECK_ERROR(igraph_community_leiden_simple(&graph, &weights, IGRAPH_LEIDEN_OBJECTIVE_CPM,
                                               1.0, 0.01, false, 1, NULL, NULL, NULL), IGRAPH_EINVAL);

    /* Invalid weight vector length. */
    igraph_vector_range(&weights, 1, igraph_ecount(&graph) + 2);
    CHECK_ERROR(igraph_community_leiden_simple(&graph, &weights, IGRAPH_LEIDEN_OBJECTIVE_MODULARITY,
                                               1.0, 0.01, false, 1, NULL, NULL, NULL), IGRAPH_EINVAL);

    igraph_destroy(&graph);

    igraph_vector_destroy(&weights);

    /* max_memberships == 1 uses the disjoint implementation path. */
    test_max_memberships_one_is_disjoint();

    test_native_nontermination_fixture();

    /* Overlapping Leiden via the unified public API. Each call reseeds the
     * RNG so that these tests are self-contained and do not perturb the
     * shared RNG stream relied upon by the (unseeded) legacy comparisons. */

    /* Zachary Karate club: with max_memberships=1 through the list form
     * (memberships-only), quality must coincide with the disjoint CPM
     * optimum found above (0.6495) because K=1 uses the disjoint driver. */
    igraph_small(&graph, 0, IGRAPH_UNDIRECTED,
                 0,  1,  0,  2,  0,  3,  0,  4,  0,  5,
                 0,  6,  0,  7,  0,  8,  0, 10,  0, 11,
                 0, 12,  0, 13,  0, 17,  0, 19,  0, 21,
                 0, 31,  1,  2,  1,  3,  1,  7,  1, 13,
                 1, 17,  1, 19,  1, 21,  1, 30,  2,  3,
                 2,  7,  2,  8,  2,  9,  2, 13,  2, 27,
                 2, 28,  2, 32,  3,  7,  3, 12,  3, 13,
                 4,  6,  4, 10,  5,  6,  5, 10,  5, 16,
                 6, 16,  8, 30,  8, 32,  8, 33,  9, 33,
                 13, 33, 14, 32, 14, 33, 15, 32, 15, 33,
                 18, 32, 18, 33, 19, 33, 20, 32, 20, 33,
                 22, 32, 22, 33, 23, 25, 23, 27, 23, 29,
                 23, 32, 23, 33, 24, 25, 24, 27, 24, 31,
                 25, 31, 26, 29, 26, 33, 27, 33, 28, 31,
                 28, 33, 29, 32, 29, 33, 30, 32, 30, 33,
                 31, 32, 31, 33, 32, 33,
                 -1);
    igraph_rng_seed(igraph_rng_default(), 0);
    run_leiden_overlapping(&graph, NULL, 0.06, 1);
    igraph_rng_seed(igraph_rng_default(), 0);
    run_leiden_overlapping(&graph, NULL, 0.06, 2);
    igraph_destroy(&graph);

    /* Disjoint union of two rings, with max_memberships=3: no bridges
     * between the rings, so the optimum stays disjoint and quality must
     * again coincide exactly with the disjoint CPM optimum (0.7500). */
    igraph_small(&graph, 20, IGRAPH_UNDIRECTED,
                 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 0, 9,
                 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 10, 19, -1);
    igraph_rng_seed(igraph_rng_default(), 0);
    run_leiden_overlapping(&graph, NULL, 0.05, 3);
    igraph_destroy(&graph);

    /* Two 5-cliques joined by a bridge vertex that connects strongly to
     * both, so it is worth its while to hold membership in both
     * communities at once: this exercises genuine overlap (the ADD/
     * SUBSTITUTE branches), not just the disjoint-equivalent K=1 case. */
    igraph_small(&graph, 11, IGRAPH_UNDIRECTED,
                 0, 1, 0, 2, 0, 3, 0, 4, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4, 3, 4,
                 5, 6, 5, 7, 5, 8, 5, 9, 6, 7, 6, 8, 6, 9, 7, 8, 7, 9, 8, 9,
                 10, 0, 10, 1, 10, 2, 10, 5, 10, 6, 10, 7,
                 -1);
    igraph_rng_seed(igraph_rng_default(), 0);
    run_leiden_overlapping(&graph, NULL, 0.2, 1);
    igraph_rng_seed(igraph_rng_default(), 0);
    run_leiden_overlapping(&graph, NULL, 0.2, 3);
    igraph_destroy(&graph);

    /* Error conditions for the unified API. */
    {
        igraph_vector_int_list_t memberships;
        igraph_vector_int_t membership;
        igraph_t directed_graph;

        igraph_vector_int_list_init(&memberships, 0);
        igraph_vector_int_init(&membership, 0);

        igraph_small(&graph, 4, IGRAPH_UNDIRECTED, 0, 1, 1, 2, 2, 3, -1);

        /* invalid max_memberships */
        CHECK_ERROR(
            igraph_community_leiden(&graph, NULL, NULL, NULL, 0.1, 0.01, 0, 0, 2,
                                    1, 0, &membership, NULL, NULL, NULL),
            IGRAPH_EINVAL);

        /* overlapping mode without memberships list */
        CHECK_ERROR(
            igraph_community_leiden(&graph, NULL, NULL, NULL, 0.1, 0.01, 2, 0, 2,
                                    1, 0, NULL, NULL, NULL, NULL),
            IGRAPH_EINVAL);

        /* directed graph */
        igraph_small(&directed_graph, 4, IGRAPH_DIRECTED, 0, 1, 1, 2, 2, 3, -1);
        CHECK_ERROR(
            igraph_community_leiden(&directed_graph, NULL, NULL, NULL, 0.1, 0.01, 2, 0, 2,
                                    1, 0, NULL, &memberships, NULL, NULL),
            IGRAPH_EINVAL);
        igraph_destroy(&directed_graph);

        igraph_destroy(&graph);
        igraph_vector_int_destroy(&membership);
        igraph_vector_int_list_destroy(&memberships);
    }

    VERIFY_FINALLY_STACK();

    return 0;
}

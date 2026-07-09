/* -*- mode: C -*-  */
/*
   IGraph library.
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

void run_leiden_CPM(const igraph_t *graph, const igraph_vector_t *edge_weights, const igraph_real_t resolution_parameter) {

    igraph_vector_int_t membership;
    igraph_integer_t nb_clusters = igraph_vcount(graph);
    igraph_real_t quality;

    /* Initialize with singleton partition. */
    igraph_vector_int_init(&membership, igraph_vcount(graph));

    igraph_community_leiden(graph, edge_weights, NULL, resolution_parameter, 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 1,
                            /*allow_isolation=*/ 1, /*only_local_moving=*/ 0,
                            &membership, /*memberships=*/ NULL, &nb_clusters, &quality);

    printf("Leiden found %" IGRAPH_PRId " clusters using CPM (resolution parameter=%.2f), quality is %.4f.\n", nb_clusters, resolution_parameter, quality);

    printf("Membership: ");
    igraph_vector_int_print(&membership);
    printf("\n");

    igraph_vector_int_destroy(&membership);
}

void run_leiden_modularity(igraph_t *graph, igraph_vector_t *edge_weights) {

    igraph_vector_int_t membership;
    igraph_vector_t strength;
    igraph_integer_t nb_clusters = igraph_vcount(graph);
    igraph_real_t quality;
    igraph_real_t m;

    igraph_vector_init(&strength, igraph_vcount(graph));
    igraph_strength(graph, &strength, igraph_vss_all(), IGRAPH_ALL, 1, edge_weights);
    m = edge_weights ? igraph_vector_sum(edge_weights) : igraph_ecount(graph);

    /* Initialize with singleton partition. */
    igraph_vector_int_init(&membership, igraph_vcount(graph));

    igraph_community_leiden(graph, edge_weights, &strength, 1.0 / (2 * m), 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 1,
                            /*allow_isolation=*/ 1, /*only_local_moving=*/ 0,
                            &membership, /*memberships=*/ NULL, &nb_clusters, &quality);

    if (isnan(quality)) {
        printf("Leiden found %" IGRAPH_PRId " clusters using modularity, quality is nan.\n", nb_clusters);
    } else {
        printf("Leiden found %" IGRAPH_PRId " clusters using modularity, quality is %.4f.\n", nb_clusters, quality);
    }

    printf("Membership: ");
    igraph_vector_int_print(&membership);
    printf("\n");

    igraph_vector_int_destroy(&membership);
    igraph_vector_destroy(&strength);
}

void run_leiden_overlapping(const igraph_t *graph, const igraph_vector_t *edge_weights,
                             const igraph_real_t resolution_parameter,
                             const igraph_integer_t max_memberships) {

    igraph_vector_int_list_t memberships;
    igraph_integer_t nb_clusters;
    igraph_real_t quality;

    igraph_vector_int_list_init(&memberships, 0);

    igraph_community_leiden(graph, edge_weights, NULL, resolution_parameter,
                            0.01, max_memberships, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*only_local_moving=*/ 0,
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
    igraph_community_leiden(&graph, NULL, NULL, 0.05, 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*only_local_moving=*/ 0,
                            &membership, /*memberships=*/ NULL, &nb_a, &quality_a);

    /* Same parameters via memberships-only (list form). */
    igraph_rng_seed(igraph_rng_default(), 42);
    igraph_community_leiden(&graph, NULL, NULL, 0.05, 0.01,
                            /*max_memberships=*/ 1, /*start=*/ 0, /*n_iterations=*/ 2,
                            /*allow_isolation=*/ 1, /*only_local_moving=*/ 0,
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
        igraph_community_leiden(&graph, NULL, NULL, 0.05, 0.01,
                                1, 0, 2, 1, 0,
                                /*membership=*/ NULL, /*memberships=*/ NULL,
                                &nb_a, &quality_a),
        IGRAPH_EINVAL);

    igraph_vector_int_destroy(&membership);
    igraph_vector_int_list_destroy(&memberships);
    igraph_destroy(&graph);

    printf("max_memberships=1 disjoint-path regression: OK\n\n");
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

    igraph_vector_destroy(&weights);

    /* max_memberships == 1 uses the disjoint implementation path. */
    test_max_memberships_one_is_disjoint();

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
            igraph_community_leiden(&graph, NULL, NULL, 0.1, 0.01, 0, 0, 2,
                                    1, 0, &membership, NULL, NULL, NULL),
            IGRAPH_EINVAL);

        /* overlapping mode without memberships list */
        CHECK_ERROR(
            igraph_community_leiden(&graph, NULL, NULL, 0.1, 0.01, 2, 0, 2,
                                    1, 0, NULL, NULL, NULL, NULL),
            IGRAPH_EINVAL);

        /* directed graph */
        igraph_small(&directed_graph, 4, IGRAPH_DIRECTED, 0, 1, 1, 2, 2, 3, -1);
        CHECK_ERROR(
            igraph_community_leiden(&directed_graph, NULL, NULL, 0.1, 0.01, 2, 0, 2,
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

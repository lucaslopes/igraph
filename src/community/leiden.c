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

/* Move vertices in order to improve the quality of a partition.
 *
 * This function considers each vertex and greedily moves it to a neighboring
 * community that maximizes the improvement in the quality of a partition.
 * Only moves that strictly improve the quality are considered.
 *
 * The vertices are examined in a queue, and initially all vertices are put in the
 * queue in a random order. Vertices are popped from the queue when they are
 * examined, and only neighbors of vertices that are moved (which are not part of
 * the cluster the vertex was moved to) are pushed to the queue again.
 *
 * The \p membership vector is used as the starting point to move around vertices,
 * and is updated in-place.
 *
 */
static igraph_error_t igraph_i_community_leiden_run_overlapping(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *node_weights,
        igraph_real_t resolution_parameter,
        igraph_real_t beta,
        igraph_int_t max_memberships,
        igraph_bool_t start,
        igraph_int_t n_iterations,
        igraph_bool_t allow_isolation,
        igraph_bool_t only_local_moving,
        igraph_vector_int_list_t *memberships,
        igraph_int_t *nb_clusters,
        igraph_real_t *quality);

static igraph_error_t leiden_fastmove_vertices(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_vertex,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        const igraph_real_t resolution,
        igraph_bool_t allow_isolation,
        igraph_int_t *nb_clusters,
        igraph_vector_int_t *membership,
        igraph_bool_t *changed) {

    const igraph_int_t n = igraph_vcount(graph);
    const igraph_bool_t directed = (vertex_in_weights != NULL);
    igraph_dqueue_int_t unstable_vertices;
    igraph_real_t max_diff, diff;
    igraph_bitset_t neighbor_cluster_added, vertex_is_stable;
    igraph_vector_t cluster_out_weights, cluster_in_weights;
    igraph_vector_t edge_weights_per_cluster;
    igraph_vector_int_t neighbor_clusters;
    igraph_vector_int_t vertex_order;
    igraph_vector_int_t nb_vertices_per_cluster;
    igraph_stack_int_t empty_clusters;
    igraph_int_t c, nb_neigh_clusters;
    int iter = 0;

    /* Initialize queue of unstable vertices and whether vertex is stable. Only
     * unstable vertices are in the queue. */
    IGRAPH_BITSET_INIT_FINALLY(&vertex_is_stable, n);

    IGRAPH_DQUEUE_INT_INIT_FINALLY(&unstable_vertices, n);

    /* Shuffle vertices */
    IGRAPH_CHECK(igraph_vector_int_init_range(&vertex_order, 0, n));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &vertex_order);
    igraph_vector_int_shuffle(&vertex_order);

    /* Add to the queue */
    for (igraph_int_t i = 0; i < n; i++) {
        IGRAPH_CHECK(igraph_dqueue_int_push(&unstable_vertices, VECTOR(vertex_order)[i]));
    }

    /* Initialize cluster weights and nb vertices */
    IGRAPH_VECTOR_INIT_FINALLY(&cluster_out_weights, n);
    if (directed) {
        IGRAPH_VECTOR_INIT_FINALLY(&cluster_in_weights, n);
    }
    IGRAPH_VECTOR_INT_INIT_FINALLY(&nb_vertices_per_cluster, n);
    for (igraph_int_t i = 0; i < n; i++) {
        c = VECTOR(*membership)[i];
        VECTOR(cluster_out_weights)[c] += VECTOR(*vertex_out_weights)[i];
        if (directed) {
            VECTOR(cluster_in_weights)[c] += VECTOR(*vertex_in_weights)[i];
        }
        VECTOR(nb_vertices_per_cluster)[c] += 1;
    }

    /* Initialize empty clusters */
    IGRAPH_STACK_INT_INIT_FINALLY(&empty_clusters, n);
    for (c = 0; c < n; c++) {
        if (VECTOR(nb_vertices_per_cluster)[c] == 0) {
            IGRAPH_CHECK(igraph_stack_int_push(&empty_clusters, c));
        }
    }

    /* Initialize vectors to be used in calculating differences */
    IGRAPH_VECTOR_INIT_FINALLY(&edge_weights_per_cluster, n);

    /* Initialize neighboring cluster */
    IGRAPH_BITSET_INIT_FINALLY(&neighbor_cluster_added, n);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&neighbor_clusters, n);

    /* Iterate while the queue is not empty */
    while (!igraph_dqueue_int_empty(&unstable_vertices)) {
        igraph_int_t v = igraph_dqueue_int_pop(&unstable_vertices);
        igraph_int_t best_cluster, current_cluster = VECTOR(*membership)[v];
        igraph_int_t degree;
        igraph_vector_int_t *edges;

        /* Remove vertex from current cluster */
        VECTOR(cluster_out_weights)[current_cluster] -= VECTOR(*vertex_out_weights)[v];
        if (directed) {
            VECTOR(cluster_in_weights)[current_cluster] -= VECTOR(*vertex_in_weights)[v];
        }
        VECTOR(nb_vertices_per_cluster)[current_cluster]--;
        if (VECTOR(nb_vertices_per_cluster)[current_cluster] == 0) {
            IGRAPH_CHECK(igraph_stack_int_push(&empty_clusters, current_cluster));
        }

        /* Find out neighboring clusters */
        if (allow_isolation) {
            c = igraph_stack_int_top(&empty_clusters);
            VECTOR(neighbor_clusters)[0] = c;
            IGRAPH_BIT_SET(neighbor_cluster_added, c);
            nb_neigh_clusters = 1;
        } else {
            nb_neigh_clusters = 0;
        }

        /* Determine the edge weight to each neighboring cluster */
        edges = igraph_inclist_get(edges_per_vertex, v);
        degree = igraph_vector_int_size(edges);
        for (igraph_int_t i = 0; i < degree; i++) {
            igraph_int_t e = VECTOR(*edges)[i];
            igraph_int_t u = IGRAPH_OTHER(graph, e, v);
            if (u != v) {
                c = VECTOR(*membership)[u];
                if (!IGRAPH_BIT_TEST(neighbor_cluster_added, c)) {
                    IGRAPH_BIT_SET(neighbor_cluster_added, c);
                    VECTOR(neighbor_clusters)[nb_neigh_clusters++] = c;
                }
                VECTOR(edge_weights_per_cluster)[c] += VECTOR(*edge_weights)[e];
            }
        }

        /* Calculate maximum diff */
        best_cluster = current_cluster;
        max_diff = VECTOR(edge_weights_per_cluster)[current_cluster];
        if (directed) {
            max_diff -=
                (VECTOR(*vertex_in_weights)[v]  * VECTOR(cluster_out_weights)[current_cluster] +
                 VECTOR(*vertex_out_weights)[v] * VECTOR(cluster_in_weights)[current_cluster]) * resolution;
        } else {
            max_diff -= VECTOR(*vertex_out_weights)[v] * VECTOR(cluster_out_weights)[current_cluster] * resolution;
        }
        for (igraph_int_t i = 0; i < nb_neigh_clusters; i++) {
            c = VECTOR(neighbor_clusters)[i];
            diff = VECTOR(edge_weights_per_cluster)[c];
            if (directed) {
                diff -= (VECTOR(*vertex_out_weights)[v] * VECTOR(cluster_in_weights)[c] +
                         VECTOR(*vertex_in_weights)[v]  * VECTOR(cluster_out_weights)[c]) * resolution;
            } else {
                diff -= VECTOR(*vertex_out_weights)[v] * VECTOR(cluster_out_weights)[c] * resolution;
            }
            /* Only consider strictly improving moves.
             * Note that this is important in considering convergence.
             */
            if (diff > max_diff) {
                best_cluster = c;
                max_diff = diff;
            }
            VECTOR(edge_weights_per_cluster)[c] = 0.0;
            IGRAPH_BIT_CLEAR(neighbor_cluster_added, c);
        }

        /* Move vertex to best cluster */
        VECTOR(cluster_out_weights)[best_cluster] += VECTOR(*vertex_out_weights)[v];
        if (directed) {
            VECTOR(cluster_in_weights)[best_cluster] += VECTOR(*vertex_in_weights)[v];
        }
        VECTOR(nb_vertices_per_cluster)[best_cluster]++;
        if (best_cluster == igraph_stack_int_top(&empty_clusters)) {
            igraph_stack_int_pop(&empty_clusters);
        }

        /* Mark vertex as stable */
        IGRAPH_BIT_SET(vertex_is_stable, v);

        /* Add stable neighbours that are not part of the new cluster to the queue */
        if (best_cluster != current_cluster) {
            *changed = true;
            VECTOR(*membership)[v] = best_cluster;

            for (igraph_int_t i = 0; i < degree; i++) {
                igraph_int_t e = VECTOR(*edges)[i];
                igraph_int_t u = IGRAPH_OTHER(graph, e, v);
                if (IGRAPH_BIT_TEST(vertex_is_stable, u) && VECTOR(*membership)[u] != best_cluster) {
                    IGRAPH_CHECK(igraph_dqueue_int_push(&unstable_vertices, u));
                    IGRAPH_BIT_CLEAR(vertex_is_stable, u);
                }
            }
        }

        IGRAPH_ALLOW_INTERRUPTION_LIMITED(iter, 1 << 14);
    }

    IGRAPH_CHECK(igraph_reindex_membership(membership, NULL, nb_clusters));

    igraph_vector_int_destroy(&neighbor_clusters);
    igraph_bitset_destroy(&neighbor_cluster_added);
    igraph_vector_destroy(&edge_weights_per_cluster);
    igraph_stack_int_destroy(&empty_clusters);
    igraph_vector_int_destroy(&nb_vertices_per_cluster);
    if (directed) igraph_vector_destroy(&cluster_in_weights);
    igraph_vector_destroy(&cluster_out_weights);
    igraph_vector_int_destroy(&vertex_order);
    igraph_dqueue_int_destroy(&unstable_vertices);
    igraph_bitset_destroy(&vertex_is_stable);
    if (directed) {
        IGRAPH_FINALLY_CLEAN(10);
    } else {
        IGRAPH_FINALLY_CLEAN(9);
    }

    return IGRAPH_SUCCESS;
}

/* Clean a refined membership vector.
 *
 * This function examines all vertices in \p vertex_subset and updates
 * \p refined_membership to ensure that the clusters are numbered consecutively,
 * starting from \p nb_refined_clusters. The \p nb_refined_clusters is also
 * updated itself. If C is the initial \p nb_refined_clusters and C' the
 * resulting \p nb_refined_clusters, then vertices in \p vertex_subset are numbered
 * C, C + 1, ..., C' - 1.
 */
static igraph_error_t leiden_clean_refined_membership(
        const igraph_vector_int_t* vertex_subset,
        igraph_vector_int_t *refined_membership,
        igraph_int_t* nb_refined_clusters) {

    const igraph_int_t n = igraph_vector_int_size(vertex_subset);
    igraph_vector_int_t new_cluster;

    IGRAPH_VECTOR_INT_INIT_FINALLY(&new_cluster, n);

    /* Clean clusters. We will store the new cluster + 1 so that cluster == 0
     * indicates that no membership was assigned yet. */
    *nb_refined_clusters += 1;
    for (igraph_int_t i = 0; i < n; i++) {
        igraph_int_t v = VECTOR(*vertex_subset)[i];
        igraph_int_t c = VECTOR(*refined_membership)[v];
        if (VECTOR(new_cluster)[c] == 0) {
            VECTOR(new_cluster)[c] = *nb_refined_clusters;
            *nb_refined_clusters += 1;
        }
    }

    /* Assign new cluster */
    for (igraph_int_t i = 0; i < n; i++) {
        igraph_int_t v = VECTOR(*vertex_subset)[i];
        igraph_int_t c = VECTOR(*refined_membership)[v];
        VECTOR(*refined_membership)[v] = VECTOR(new_cluster)[c] - 1;
    }
    /* We used the cluster + 1, so correct */
    *nb_refined_clusters -= 1;

    igraph_vector_int_destroy(&new_cluster);
    IGRAPH_FINALLY_CLEAN(1);

    return IGRAPH_SUCCESS;
}

/* Merge vertices for a subset of the vertices. This is used to refine a partition.
 *
 * The vertices included in \p vertex_subset are assumed to be the vertices i for which
 * membership[i] = cluster_subset.
 *
 * All vertices in \p vertex_subset are initialized to a singleton partition in \p
 * refined_membership. Only singleton clusters can be merged if they are
 * sufficiently well connected to the current subgraph induced by \p
 * vertex_subset.
 *
 * We only examine each vertex once. Instead of greedily choosing the maximum
 * possible cluster to merge with, the cluster is chosen randomly among all
 * possibilities that do not decrease the quality of the partition. The
 * probability of choosing a certain cluster is proportional to exp(diff/beta).
 * For beta to 0 this converges to selecting a cluster with the maximum
 * improvement. For beta to infinity this converges to a uniform distribution
 * among all eligible clusters.
 *
 * The \p refined_membership is updated for vertex in \p vertex_subset. The number
 * of refined clusters, \p nb_refined_clusters is used to set the actual refined
 * cluster membership and is updated after this routine. Within each cluster
 * (i.e. for a given \p vertex_subset), the refined membership is initially simply
 * set to 0, ..., n - 1 (for n vertices in \p vertex_subset). However, for each \p
 * vertex_subset the refined membership should of course be unique. Hence, after
 * merging, the refined membership starts with \p nb_refined_clusters, which is
 * also updated to ensure that the resulting \p nb_refined_clusters counts all
 * refined clusters that have already been processed. See
 * leiden_clean_refined_membership for more information about
 * this aspect.
 */
static igraph_error_t leiden_merge_vertices(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_vertex,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        const igraph_vector_int_t *vertex_subset,
        const igraph_vector_int_t *membership,
        const igraph_int_t cluster_subset,
        const igraph_real_t resolution,
        const igraph_real_t beta,
        igraph_int_t *nb_refined_clusters,
        igraph_vector_int_t *refined_membership) {

    const igraph_bool_t directed = (vertex_in_weights != NULL);
    igraph_vector_int_t vertex_order;
    igraph_bitset_t non_singleton_cluster, neighbor_cluster_added;
    igraph_real_t max_diff, total_cum_trans_diff, diff;
    igraph_real_t total_vertex_out_weight = 0.0, total_vertex_in_weight = 0.0;
    const igraph_int_t n = igraph_vector_int_size(vertex_subset);
    igraph_vector_t cluster_out_weights, cluster_in_weights;
    igraph_vector_t cum_trans_diff, edge_weights_per_cluster, external_edge_weight_per_cluster_in_subset;
    igraph_vector_int_t neighbor_clusters;
    igraph_vector_int_t *edges, nb_vertices_per_cluster;
    igraph_int_t degree, nb_neigh_clusters;

    /* Initialize cluster weights */
    IGRAPH_VECTOR_INIT_FINALLY(&cluster_out_weights, n);
    if (directed) {
        IGRAPH_VECTOR_INIT_FINALLY(&cluster_in_weights, n);
    }

    /* Initialize number of vertices per cluster */
    IGRAPH_VECTOR_INT_INIT_FINALLY(&nb_vertices_per_cluster, n);

    /* Initialize external edge weight per cluster in subset */
    IGRAPH_VECTOR_INIT_FINALLY(&external_edge_weight_per_cluster_in_subset, n);

    /* Initialize administration for a singleton partition */
    for (igraph_int_t i = 0; i < n; i++) {
        igraph_int_t v = VECTOR(*vertex_subset)[i];
        VECTOR(*refined_membership)[v] = i;
        VECTOR(cluster_out_weights)[i] += VECTOR(*vertex_out_weights)[v];
        total_vertex_out_weight += VECTOR(*vertex_out_weights)[v];
        if (directed) {
            VECTOR(cluster_in_weights)[i] += VECTOR(*vertex_in_weights)[v];
            total_vertex_in_weight += VECTOR(*vertex_in_weights)[v];
        }
        VECTOR(nb_vertices_per_cluster)[i] += 1;

        /* Find out neighboring clusters */
        edges = igraph_inclist_get(edges_per_vertex, v);
        degree = igraph_vector_int_size(edges);
        for (igraph_int_t j = 0; j < degree; j++) {
            igraph_int_t e = VECTOR(*edges)[j];
            igraph_int_t u = IGRAPH_OTHER(graph, e, v);
            if (u != v && VECTOR(*membership)[u] == cluster_subset) {
                VECTOR(external_edge_weight_per_cluster_in_subset)[i] += VECTOR(*edge_weights)[e];
            }
        }
    }

    /* Shuffle vertices */
    IGRAPH_CHECK(igraph_vector_int_init_copy(&vertex_order, vertex_subset));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &vertex_order);
    igraph_vector_int_shuffle(&vertex_order);

    /* Initialize non singleton clusters */
    IGRAPH_BITSET_INIT_FINALLY(&non_singleton_cluster, n);

    /* Initialize vectors to be used in calculating differences */
    IGRAPH_VECTOR_INIT_FINALLY(&edge_weights_per_cluster, n);

    /* Initialize neighboring cluster */
    IGRAPH_BITSET_INIT_FINALLY(&neighbor_cluster_added, n);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&neighbor_clusters, n);

    /* Initialize cumulative transformed difference */
    IGRAPH_VECTOR_INIT_FINALLY(&cum_trans_diff, n);

    for (igraph_int_t i = 0; i < n; i++) {
        igraph_int_t v = VECTOR(vertex_order)[i];
        igraph_int_t chosen_cluster, best_cluster, current_cluster = VECTOR(*refined_membership)[v];
        igraph_real_t vertex_weight_prod;

        if (directed) {
            vertex_weight_prod =
                VECTOR(cluster_out_weights)[current_cluster] * (total_vertex_in_weight - VECTOR(cluster_in_weights)[current_cluster]) +
                VECTOR(cluster_in_weights)[current_cluster] * (total_vertex_out_weight - VECTOR(cluster_out_weights)[current_cluster]);
        } else {
            vertex_weight_prod = VECTOR(cluster_out_weights)[current_cluster] * (total_vertex_out_weight - VECTOR(cluster_out_weights)[current_cluster]);
        }

        if (!IGRAPH_BIT_TEST(non_singleton_cluster, current_cluster) &&
            (VECTOR(external_edge_weight_per_cluster_in_subset)[current_cluster] >=
             vertex_weight_prod * resolution)) {
            /* Remove vertex from current cluster, which is then a singleton by
             * definition. */
            VECTOR(cluster_out_weights)[current_cluster] = 0.0;
            if (directed) {
                VECTOR(cluster_in_weights)[current_cluster] = 0.0;
            }
            VECTOR(nb_vertices_per_cluster)[current_cluster] = 0;

            /* Find out neighboring clusters */
            edges = igraph_inclist_get(edges_per_vertex, v);
            degree = igraph_vector_int_size(edges);

            /* Also add current cluster to ensure it can be chosen. */
            VECTOR(neighbor_clusters)[0] = current_cluster;
            IGRAPH_BIT_SET(neighbor_cluster_added, current_cluster);
            nb_neigh_clusters = 1;
            for (igraph_int_t j = 0; j < degree; j++) {
                igraph_int_t e = VECTOR(*edges)[j];
                igraph_int_t u = IGRAPH_OTHER(graph, e, v);
                if (u != v && VECTOR(*membership)[u] == cluster_subset) {
                    igraph_int_t c = VECTOR(*refined_membership)[u];
                    if (!IGRAPH_BIT_TEST(neighbor_cluster_added, c)) {
                        IGRAPH_BIT_SET(neighbor_cluster_added, c);
                        VECTOR(neighbor_clusters)[nb_neigh_clusters++] = c;
                    }
                    VECTOR(edge_weights_per_cluster)[c] += VECTOR(*edge_weights)[e];
                }
            }

            /* Calculate diffs */
            best_cluster = current_cluster;
            max_diff = 0.0;
            total_cum_trans_diff = 0.0;
            for (igraph_int_t j = 0; j < nb_neigh_clusters; j++) {
                igraph_int_t c = VECTOR(neighbor_clusters)[j];

                if (directed) {
                    vertex_weight_prod =
                        VECTOR(cluster_out_weights)[c] * (total_vertex_in_weight - VECTOR(cluster_in_weights)[c]) +
                        VECTOR(cluster_in_weights)[c] * (total_vertex_out_weight - VECTOR(cluster_out_weights)[c]);
                } else {
                    vertex_weight_prod = VECTOR(cluster_out_weights)[c] * (total_vertex_out_weight - VECTOR(cluster_out_weights)[c]);
                }

                if (VECTOR(external_edge_weight_per_cluster_in_subset)[c] >= vertex_weight_prod * resolution) {
                    diff = VECTOR(edge_weights_per_cluster)[c];
                    if (directed) {
                        diff -= (VECTOR(*vertex_out_weights)[v] * VECTOR(cluster_in_weights)[c] +
                                 VECTOR(*vertex_in_weights)[v] * VECTOR(cluster_out_weights)[c]) * resolution;
                    } else {
                        diff -= VECTOR(*vertex_out_weights)[v] * VECTOR(cluster_out_weights)[c] * resolution;
                    }


                    if (diff > max_diff) {
                        best_cluster = c;
                        max_diff = diff;
                    }

                    /* Calculate the transformed difference for sampling */
                    if (diff >= 0) {
                        total_cum_trans_diff += exp(diff / beta);
                    }

                }

                VECTOR(cum_trans_diff)[j] = total_cum_trans_diff;
                VECTOR(edge_weights_per_cluster)[c] = 0.0;
                IGRAPH_BIT_CLEAR(neighbor_cluster_added, c);
            }

            /* Determine the neighboring cluster to which the currently selected vertex
             * will be moved.
             */
            if (total_cum_trans_diff < IGRAPH_INFINITY) {
                igraph_real_t r = RNG_UNIF(0, total_cum_trans_diff);
                igraph_int_t chosen_idx;
                igraph_vector_binsearch_slice(&cum_trans_diff, r, &chosen_idx, 0, nb_neigh_clusters);
                chosen_cluster = VECTOR(neighbor_clusters)[chosen_idx];
            } else {
                chosen_cluster = best_cluster;
            }

            /* Move vertex to randomly chosen cluster */
            VECTOR(cluster_out_weights)[chosen_cluster] += VECTOR(*vertex_out_weights)[v];
            if (directed) {
                VECTOR(cluster_in_weights)[chosen_cluster] += VECTOR(*vertex_in_weights)[v];
            }
            VECTOR(nb_vertices_per_cluster)[chosen_cluster]++;

            for (igraph_int_t j = 0; j < degree; j++) {
                igraph_int_t e = VECTOR(*edges)[j];
                igraph_int_t u = IGRAPH_OTHER(graph, e, v);
                if (VECTOR(*membership)[u] == cluster_subset) {
                    if (VECTOR(*refined_membership)[u] == chosen_cluster) {
                        VECTOR(external_edge_weight_per_cluster_in_subset)[chosen_cluster] -= VECTOR(*edge_weights)[e];
                    } else {
                        VECTOR(external_edge_weight_per_cluster_in_subset)[chosen_cluster] += VECTOR(*edge_weights)[e];
                    }
                }
            }

            /* Set cluster  */
            if (chosen_cluster != current_cluster) {
                VECTOR(*refined_membership)[v] = chosen_cluster;

                IGRAPH_BIT_SET(non_singleton_cluster, chosen_cluster);
            }
        } /* end if singleton and may be merged */
    }

    IGRAPH_CHECK(leiden_clean_refined_membership(vertex_subset, refined_membership, nb_refined_clusters));

    igraph_vector_destroy(&cum_trans_diff);
    igraph_vector_int_destroy(&neighbor_clusters);
    igraph_bitset_destroy(&neighbor_cluster_added);
    igraph_vector_destroy(&edge_weights_per_cluster);
    igraph_bitset_destroy(&non_singleton_cluster);
    igraph_vector_int_destroy(&vertex_order);
    igraph_vector_destroy(&external_edge_weight_per_cluster_in_subset);
    igraph_vector_int_destroy(&nb_vertices_per_cluster);
    if (directed) igraph_vector_destroy(&cluster_in_weights);
    igraph_vector_destroy(&cluster_out_weights);
    if (directed) {
        IGRAPH_FINALLY_CLEAN(10);
    } else {
        IGRAPH_FINALLY_CLEAN(9);
    }

    return IGRAPH_SUCCESS;
}

/* Create clusters out of a membership vector.
 *
 * It is assumed that the incoming list of integer vectors is already sized
 * appropriately (i.e. it has at least as many items as the number of clusters
 * in the membership vector), and that each item in the list of integer vectors
 * is empty.
 */
static igraph_error_t leiden_get_clusters(
        const igraph_vector_int_t *membership,
        igraph_vector_int_list_t *clusters) {

    const igraph_int_t n = igraph_vector_int_size(membership);

    for (igraph_int_t i = 0; i < n; i++) {
        /* Get cluster for vertex i */
        igraph_vector_int_t *cluster = igraph_vector_int_list_get_ptr(clusters, VECTOR(*membership)[i]);

        /* Add vertex i to cluster vector */
        IGRAPH_CHECK(igraph_vector_int_push_back(cluster, i));
    }

    return IGRAPH_SUCCESS;
}

/* Aggregate the graph based on the \p refined membership while setting the
 * membership of each aggregated vertex according to the \p membership.
 *
 * Technically speaking we have that
 * aggregated_membership[refined_membership[v]] = membership[v] for each vertex v.
 *
 * The new aggregated graph is returned in \p aggregated_graph. This graph
 * object should not yet be initialized, igraph_create() is called on it, and
 * responsibility for destroying the object lies with the calling method
 *
 * The remaining results, aggregated_edge_weights, aggregate_vertex_weights and
 * aggregated_membership are all expected to be initialized.
 *
 */
static igraph_error_t leiden_aggregate(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_vertex,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        const igraph_vector_int_t *membership,
        const igraph_vector_int_t *refined_membership,
        const igraph_int_t nb_refined_clusters,
        igraph_t *aggregated_graph,
        igraph_vector_t *aggregated_edge_weights,
        igraph_vector_t *aggregated_vertex_out_weights,
        igraph_vector_t *aggregated_vertex_in_weights,
        igraph_vector_int_t *aggregated_membership) {

    const igraph_bool_t directed = (vertex_in_weights != NULL);
    igraph_vector_int_t aggregated_edges;
    igraph_vector_t edge_weight_to_cluster;
    igraph_vector_int_list_t refined_clusters;
    igraph_vector_int_t *incident_edges;
    igraph_vector_int_t neighbor_clusters;
    igraph_bitset_t neighbor_cluster_added;
    igraph_int_t c, degree, nb_neigh_clusters;

    /* Get refined clusters */
    IGRAPH_VECTOR_INT_LIST_INIT_FINALLY(&refined_clusters, nb_refined_clusters);
    IGRAPH_CHECK(leiden_get_clusters(refined_membership, &refined_clusters));

    /* Initialize new edges */
    IGRAPH_VECTOR_INT_INIT_FINALLY(&aggregated_edges, 0);

    /* We clear the aggregated edge weights, we will push each new edge weight */
    igraph_vector_clear(aggregated_edge_weights);
    /* Simply resize the aggregated vertex weights and membership, they can be set directly */
    IGRAPH_CHECK(igraph_vector_resize(aggregated_vertex_out_weights, nb_refined_clusters));
    if (directed) {
        IGRAPH_CHECK(igraph_vector_resize(aggregated_vertex_in_weights, nb_refined_clusters));
    }
    IGRAPH_CHECK(igraph_vector_int_resize(aggregated_membership, nb_refined_clusters));

    IGRAPH_VECTOR_INIT_FINALLY(&edge_weight_to_cluster, nb_refined_clusters);

    /* Initialize neighboring cluster */
    IGRAPH_BITSET_INIT_FINALLY(&neighbor_cluster_added, nb_refined_clusters);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&neighbor_clusters, nb_refined_clusters);

    /* Check per cluster */
    for (c = 0; c < nb_refined_clusters; c++) {
        igraph_vector_int_t* refined_cluster = igraph_vector_int_list_get_ptr(&refined_clusters, c);
        igraph_int_t n_c = igraph_vector_int_size(refined_cluster);
        igraph_int_t v = -1;

        /* Calculate the total edge weight to other clusters */
        VECTOR(*aggregated_vertex_out_weights)[c] = 0.0;
        if (directed) {
            VECTOR(*aggregated_vertex_in_weights)[c] = 0.0;
        }
        nb_neigh_clusters = 0;
        for (igraph_int_t i = 0; i < n_c; i++) {
            v = VECTOR(*refined_cluster)[i];
            incident_edges = igraph_inclist_get(edges_per_vertex, v);
            degree = igraph_vector_int_size(incident_edges);

            for (igraph_int_t j = 0; j < degree; j++) {
                igraph_int_t e = VECTOR(*incident_edges)[j];
                igraph_int_t u = IGRAPH_OTHER(graph, e, v);
                igraph_int_t c2 = VECTOR(*refined_membership)[u];

                if (c2 > c) {
                    if (!IGRAPH_BIT_TEST(neighbor_cluster_added, c2)) {
                        IGRAPH_BIT_SET(neighbor_cluster_added, c2);
                        VECTOR(neighbor_clusters)[nb_neigh_clusters++] = c2;
                    }
                    VECTOR(edge_weight_to_cluster)[c2] += VECTOR(*edge_weights)[e];
                }
            }

            VECTOR(*aggregated_vertex_out_weights)[c] += VECTOR(*vertex_out_weights)[v];
            if (directed) {
                VECTOR(*aggregated_vertex_in_weights)[c] += VECTOR(*vertex_in_weights)[v];
            }
        }

        /* Add actual edges from this cluster to the other clusters */
        for (igraph_int_t i = 0; i < nb_neigh_clusters; i++) {
            igraph_int_t c2 = VECTOR(neighbor_clusters)[i];

            /* Add edge */
            IGRAPH_CHECK(igraph_vector_int_push_back(&aggregated_edges, c));
            IGRAPH_CHECK(igraph_vector_int_push_back(&aggregated_edges, c2));

            /* Add edge weight */
            IGRAPH_CHECK(igraph_vector_push_back(aggregated_edge_weights, VECTOR(edge_weight_to_cluster)[c2]));

            VECTOR(edge_weight_to_cluster)[c2] = 0.0;
            IGRAPH_BIT_CLEAR(neighbor_cluster_added, c2);
        }

        VECTOR(*aggregated_membership)[c] = VECTOR(*membership)[v];

    }

    igraph_vector_int_destroy(&neighbor_clusters);
    igraph_bitset_destroy(&neighbor_cluster_added);
    igraph_vector_destroy(&edge_weight_to_cluster);
    igraph_vector_int_list_destroy(&refined_clusters);
    IGRAPH_FINALLY_CLEAN(4);

    igraph_destroy(aggregated_graph);
    IGRAPH_CHECK(igraph_create(aggregated_graph, &aggregated_edges, nb_refined_clusters,
                               directed));

    igraph_vector_int_destroy(&aggregated_edges);
    IGRAPH_FINALLY_CLEAN(1);

    return IGRAPH_SUCCESS;
}

/* Calculate the quality of the partition.
 *
 * The quality is defined as
 *
 * 1 / 2m sum_ij (A_ij - gamma n_i n_j) d(s_i, s_j)
 *
 * for undirected graphs and as
 *
 * 1 / m sum_ij (A_ij - gamma n^out_i n^in_j) d(s_i, s_j)
 *
 * where m is the total edge weight, A_ij is the weight of edge (i, j), gamma is
 * the so-called resolution parameter, n_i is the vertex weight of vertex i, s_i is
 * the cluster of vertex i and d(x, y) = 1 if and only if x = y and 0 otherwise.
 *
 * Note that by setting n_i = k_i the degree of vertex i and dividing gamma by 2m,
 * we effectively optimize modularity. By setting n_i = 1 we optimize the
 * Constant Potts Model.
 *
 * This can be represented as a sum over clusters as
 *
 * 1 / 2m sum_c (e_c - gamma N_c^2)
 *
 * where e_c = sum_ij A_ij d(s_i, c)d(s_j, c) is the internal edge weight
 * in cluster c (or twice this value if undirected) and
 * N_c = sum_i n_i d(s_i, c) is the sum of the vertex weights inside cluster c.
 * This is how the quality is calculated in practice.
 */
static igraph_error_t leiden_quality(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *vertex_out_weights,
        const igraph_vector_t *vertex_in_weights,
        const igraph_vector_int_t *membership,
        const igraph_int_t nb_clusters,
        const igraph_real_t resolution,
        igraph_real_t *quality) {

    const igraph_int_t vcount = igraph_vcount(graph);
    const igraph_int_t ecount = igraph_ecount(graph);
    const igraph_bool_t directed = (vertex_in_weights != NULL);
    const igraph_real_t directed_multiplier = directed ? 1.0 : 2.0;
    igraph_vector_t cluster_out_weights, cluster_in_weights;
    igraph_real_t total_edge_weight = 0.0;

    *quality = 0.0;

    for (igraph_int_t e=0; e < ecount; e++) {
        igraph_int_t from = IGRAPH_FROM(graph, e);
        igraph_int_t to = IGRAPH_TO(graph, e);
        total_edge_weight += VECTOR(*edge_weights)[e];

        /* We add the internal edge weights. */
        if (VECTOR(*membership)[from] == VECTOR(*membership)[to]) {
            *quality += directed_multiplier * VECTOR(*edge_weights)[e];
        }
    }

    /* Initialize and compute cluster weights. */

    IGRAPH_VECTOR_INIT_FINALLY(&cluster_out_weights, vcount);
    if (directed) {
        IGRAPH_VECTOR_INIT_FINALLY(&cluster_in_weights, vcount);
    }

    for (igraph_int_t i = 0; i < vcount; i++) {
        igraph_int_t c = VECTOR(*membership)[i];
        VECTOR(cluster_out_weights)[c] += VECTOR(*vertex_out_weights)[i];
        if (directed) {
            VECTOR(cluster_in_weights)[c] += VECTOR(*vertex_in_weights)[i];
        }
    }

    /* We subtract gamma * N^out_c * N^in_c */

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

    /* We normalise by m or 2m depending on directedness */
    *quality /= (directed_multiplier * total_edge_weight);

    return IGRAPH_SUCCESS;
}

/* This is the core of the Leiden algorithm and relies on subroutines to
 * perform the three different phases: (1) local moving of vertices, (2)
 * refinement of the partition and (3) aggregation of the network based on the
 * refined partition, using the non-refined partition to create an initial
 * partition for the aggregate network.
 */
static igraph_error_t community_leiden(
        const igraph_t *graph,
        igraph_vector_t *edge_weights,
        igraph_vector_t *vertex_out_weights,
        igraph_vector_t *vertex_in_weights,
        igraph_real_t resolution,
        igraph_real_t beta,
        igraph_bool_t allow_isolation,
        igraph_bool_t only_local_moving,
        igraph_vector_int_t *membership,
        igraph_int_t *nb_clusters,
        igraph_real_t *quality,
        igraph_bool_t *changed) {

    const igraph_int_t n = igraph_vcount(graph);
    const igraph_bool_t directed = (vertex_in_weights != NULL);
    igraph_int_t nb_refined_clusters;
    igraph_int_t i, c;
    igraph_t aggregated_graph, *i_graph;
    igraph_vector_t aggregated_edge_weights;
    igraph_vector_t aggregated_vertex_out_weights, aggregated_vertex_in_weights;
    igraph_vector_int_t aggregated_membership;
    igraph_vector_t *i_edge_weights;
    igraph_vector_t *i_vertex_out_weights, *i_vertex_in_weights;
    igraph_vector_int_t *i_membership;
    igraph_vector_t tmp_edge_weights, tmp_vertex_out_weights, tmp_vertex_in_weights;
    igraph_vector_int_t tmp_membership;
    igraph_vector_int_t refined_membership;
    igraph_vector_int_t aggregate_vertex;
    igraph_vector_int_list_t clusters;
    igraph_inclist_t edges_per_vertex;
    igraph_bool_t continue_clustering;
    igraph_int_t level = 0;

    /* Initialize temporary weights and membership to be used in aggregation */
    IGRAPH_VECTOR_INIT_FINALLY(&tmp_edge_weights, 0);
    IGRAPH_VECTOR_INIT_FINALLY(&tmp_vertex_out_weights, 0);
    if (directed) {
        IGRAPH_VECTOR_INIT_FINALLY(&tmp_vertex_in_weights, 0);
    }
    IGRAPH_VECTOR_INT_INIT_FINALLY(&tmp_membership, 0);

    /* Initialize clusters */
    IGRAPH_VECTOR_INT_LIST_INIT_FINALLY(&clusters, n);

    /* Initialize aggregate vertices, which initially is identical to simply the
     * vertices in the graph. */
    IGRAPH_CHECK(igraph_vector_int_init_range(&aggregate_vertex, 0, n));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &aggregate_vertex);

    /* Initialize refined membership */
    IGRAPH_VECTOR_INT_INIT_FINALLY(&refined_membership, 0);

    /* Initialize aggregated graph */
    IGRAPH_CHECK(igraph_empty(&aggregated_graph, 0, directed));
    IGRAPH_FINALLY(igraph_destroy, &aggregated_graph);

    /* Initialize aggregated edge weights */
    IGRAPH_VECTOR_INIT_FINALLY(&aggregated_edge_weights, 0);

    /* Initialize aggregated vertex weights */
    IGRAPH_VECTOR_INIT_FINALLY(&aggregated_vertex_out_weights, 0);
    if (directed) {
        IGRAPH_VECTOR_INIT_FINALLY(&aggregated_vertex_in_weights, 0);
    }

    /* Initialize aggregated membership */
    IGRAPH_VECTOR_INT_INIT_FINALLY(&aggregated_membership, 0);

    /* Set actual graph, weights and membership to be used. */
    i_graph = (igraph_t*)graph;
    i_edge_weights = edge_weights;
    i_vertex_out_weights = vertex_out_weights;
    i_vertex_in_weights = directed ? vertex_in_weights : NULL;
    i_membership = membership;

    /* Clean membership: ensure that cluster indices are 0 <= c < n. */
    IGRAPH_CHECK(igraph_reindex_membership(i_membership, NULL, nb_clusters));

    /* We start out with no changes, whenever a vertex is moved, this will be set to true. */
    *changed = false;
    do {

        /* Get incidence list for fast iteration */
        IGRAPH_CHECK(igraph_inclist_init( i_graph, &edges_per_vertex, IGRAPH_ALL, IGRAPH_LOOPS_TWICE));
        IGRAPH_FINALLY(igraph_inclist_destroy, &edges_per_vertex);

        /* Move around the vertices in order to increase the quality */
        IGRAPH_CHECK(leiden_fastmove_vertices(i_graph,
                                              &edges_per_vertex,
                                              i_edge_weights,
                                              i_vertex_out_weights, i_vertex_in_weights,
                                              resolution,
                                              allow_isolation,
                                              nb_clusters,
                                              i_membership,
                                              changed));

        /* We only continue clustering if not all clusters are represented by a
         * single vertex yet and only_local_moving is false.
         */
        continue_clustering = only_local_moving ? !only_local_moving : (*nb_clusters < igraph_vcount(i_graph));

        if (continue_clustering) {
            /* Set original membership */
            if (level > 0) {
                for (i = 0; i < n; i++) {
                    igraph_int_t v_aggregate = VECTOR(aggregate_vertex)[i];
                    VECTOR(*membership)[i] = VECTOR(*i_membership)[v_aggregate];
                }
            }

            /* Get vertex sets for each cluster. */
            IGRAPH_CHECK(leiden_get_clusters(i_membership, &clusters));

            /* Ensure refined membership is correct size */
            IGRAPH_CHECK(igraph_vector_int_resize(&refined_membership, igraph_vcount(i_graph)));

            /* Refine each cluster */
            nb_refined_clusters = 0;
            for (c = 0; c < *nb_clusters; c++) {
                igraph_vector_int_t* cluster = igraph_vector_int_list_get_ptr(&clusters, c);
                IGRAPH_CHECK(leiden_merge_vertices(i_graph,
                                                   &edges_per_vertex,
                                                   i_edge_weights,
                                                   i_vertex_out_weights, i_vertex_in_weights,
                                                   cluster, i_membership, c,
                                                   resolution, beta,
                                                   &nb_refined_clusters, &refined_membership));
                /* Empty cluster */
                igraph_vector_int_clear(cluster);
            }

            /* If refinement didn't aggregate anything, we aggregate on the basis of
             * the actual clustering */
            if (nb_refined_clusters >= igraph_vcount(i_graph)) {
                IGRAPH_CHECK(igraph_vector_int_update(&refined_membership, i_membership));
                nb_refined_clusters = *nb_clusters;
            }

            /* Keep track of aggregate vertex. */
            for (i = 0; i < n; i++) {
                /* Current aggregate vertex */
                igraph_int_t v_aggregate = VECTOR(aggregate_vertex)[i];
                /* New aggregate vertex */
                VECTOR(aggregate_vertex)[i] = VECTOR(refined_membership)[v_aggregate];
            }

            IGRAPH_CHECK(leiden_aggregate(
                i_graph,
                &edges_per_vertex,
                i_edge_weights,
                i_vertex_out_weights, i_vertex_in_weights,
                i_membership, &refined_membership, nb_refined_clusters,
                &aggregated_graph,
                &tmp_edge_weights,
                &tmp_vertex_out_weights, directed ? &tmp_vertex_in_weights : NULL,
                &tmp_membership));

            /* On the lowest level, the actual graph and vertex and edge weights and
             * membership are used. On higher levels, we will use the aggregated graph
             * and associated vectors.
             */
            if (level == 0) {
                /* Set actual graph, weights and membership to be used. */
                i_graph = &aggregated_graph;
                i_edge_weights = &aggregated_edge_weights;
                i_vertex_out_weights = &aggregated_vertex_out_weights;
                if (directed) {
                    i_vertex_in_weights = &aggregated_vertex_in_weights;
                }
                i_membership = &aggregated_membership;
            }

            /* Update the aggregated administration. */
            IGRAPH_CHECK(igraph_vector_update(i_edge_weights, &tmp_edge_weights));
            IGRAPH_CHECK(igraph_vector_update(i_vertex_out_weights, &tmp_vertex_out_weights));
            if (directed) {
                IGRAPH_CHECK(igraph_vector_update(i_vertex_in_weights, &tmp_vertex_in_weights));
            }
            IGRAPH_CHECK(igraph_vector_int_update(i_membership, &tmp_membership));

            level += 1;
        }

        /* We are done iterating, so we destroy the incidence list */
        igraph_inclist_destroy(&edges_per_vertex);
        IGRAPH_FINALLY_CLEAN(1);
    } while (continue_clustering);

    /* Free aggregated graph and associated vectors */
    igraph_vector_int_destroy(&aggregated_membership);
    if (directed) igraph_vector_destroy(&aggregated_vertex_in_weights);
    igraph_vector_destroy(&aggregated_vertex_out_weights);
    igraph_vector_destroy(&aggregated_edge_weights);
    igraph_destroy(&aggregated_graph);

    /* Free remaining memory */
    igraph_vector_int_destroy(&refined_membership);
    igraph_vector_int_destroy(&aggregate_vertex);
    igraph_vector_int_list_destroy(&clusters);
    igraph_vector_int_destroy(&tmp_membership);
    igraph_vector_destroy(&tmp_vertex_out_weights);
    if (directed) igraph_vector_destroy(&tmp_vertex_in_weights);
    igraph_vector_destroy(&tmp_edge_weights);

    if (directed) {
        IGRAPH_FINALLY_CLEAN(12);
    } else {
        IGRAPH_FINALLY_CLEAN(10);
    }

    /* Calculate quality */
    if (quality) {
        IGRAPH_CHECK(leiden_quality(graph,
                                    edge_weights, vertex_out_weights, vertex_in_weights,
                                    membership,
                                    *nb_clusters, resolution,
                                    quality));
    }

    return IGRAPH_SUCCESS;
}

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
 * Leiden algorithm, only vertices whose neighborhood has changed are visited. Only
 * moves that strictly improve the quality function are made. The refinement is
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
 * \param graph The input graph.
 * \param edge_weights Numeric vector containing edge weights. If \c NULL,
 *    every edge has equal weight of 1. The weights need not be non-negative.
 * \param vertex_out_weights Numeric vector containing vertex weights, or vertex
 *    out-weights for directed graphs. If \c NULL, every vertex has equal
 *    weight of 1.
 * \param vertex_in_weights Numeric vector containing vertex in-weights for
 *    directed graphs. If set to \c NULL, in-weights are assumed to be the same
 *    as out-weights, which effectively ignores edge directions.
 *    Must be \c NULL for undirected graphs.
 * \param n_iterations Iterate the core Leiden algorithm the indicated number
 *    of times. If this is a negative number, it will continue iterating until
 *    an iteration did not change the clustering. Two iterations are often
 *    sufficient, thus 2 is a reasonable default.
 * \param beta The randomness used in the refinement step when merging. A small
 *    amount of randomness (\c beta = 0.01) typically works well.
 * \param start Start from membership vector. If this is true, the optimization
 *    will start from the provided membership vector. If this is false, the
 *    optimization will start from a singleton partition.
 * \param n_iterations Iterate the core Leiden algorithm for the indicated number
 *    of times. If this is a negative number, it will continue iterating until
 *    an iteration did not change the clustering.
 * \param membership The membership vector. This is both used as the initial
 *    membership from which optimisation starts and is updated in place. It
 *    must hence be properly initialized. When finding clusters from scratch it
 *    is typically started using a singleton clustering. This can be achieved
 *    using \ref igraph_vector_int_init_range().
 * \param nb_clusters The number of clusters contained in the final \p membership.
 *    If \c NULL, the number of clusters will not be returned.
 * \param quality The quality of the partition, in terms of the objective
 *    function as included in the documentation. If \c NULL the quality will
 *    not be calculated.
 * \return Error code.
 *
 * Time complexity: near linear on sparse graphs.
 *
 * \sa \ref igraph_community_leiden_simple() for a simplified interface
 * that allows specifying an objective function directly and does not require
 * vertex weights.
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
        igraph_bool_t only_local_moving,
        igraph_vector_int_t *membership,
        igraph_vector_int_list_t *memberships,
        igraph_int_t *nb_clusters,
        igraph_real_t *quality) {

    const igraph_int_t vcount = igraph_vcount(graph);
    const igraph_int_t ecount = igraph_ecount(graph);
    const igraph_bool_t directed = igraph_is_directed(graph);

    if (max_memberships < 1) {
        IGRAPH_ERROR("max_memberships must be at least 1.", IGRAPH_EINVAL);
    }

    if (max_memberships == 1) {
        /* Disjoint path */
        igraph_vector_t *i_edge_weights, *i_vertex_out_weights, *i_vertex_in_weights;
        igraph_int_t i_nb_clusters;
        igraph_vector_int_t *mem = membership;
        igraph_vector_int_t mem_temp;
        igraph_bool_t use_temp = !membership;

        if (!nb_clusters) {
            nb_clusters = &i_nb_clusters;
        }

        if (use_temp) {
            if (!memberships) {
                IGRAPH_ERROR("Either membership or memberships must be provided.", IGRAPH_EINVAL);
            }
            IGRAPH_CHECK(igraph_vector_int_init(&mem_temp, vcount));
            IGRAPH_FINALLY(igraph_vector_int_destroy, &mem_temp);
            mem = &mem_temp;
            if (start) {
                /* Try to populate initial from memberships if possible, or keep as singleton */
                if (igraph_vector_int_list_size(memberships) == vcount) {
                    for (igraph_int_t v = 0; v < vcount; v++) {
                        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
                        VECTOR(*mem)[v] = igraph_vector_int_size(sigma) > 0 ? VECTOR(*sigma)[0] : v;
                    }
                } else {
                    IGRAPH_CHECK(igraph_vector_int_range(mem, 0, vcount));
                }
            } else {
                IGRAPH_CHECK(igraph_vector_int_range(mem, 0, vcount));
            }
        } else {
            if (start) {
                if (igraph_vector_int_size(membership) != vcount) {
                    IGRAPH_ERROR("Membership vector length does not equal the number of vertices.", IGRAPH_EINVAL);
                }
            } else {
                IGRAPH_CHECK(igraph_vector_int_range(membership, 0, vcount));
            }
        }

        /* Check edge weights to possibly use default. */
        if (!edge_weights) {
            i_edge_weights = IGRAPH_CALLOC(1, igraph_vector_t);
            IGRAPH_CHECK_OOM(i_edge_weights, "Leiden algorithm failed, could not allocate memory for edge weights.");
            IGRAPH_FINALLY(igraph_free, i_edge_weights);
            IGRAPH_CHECK(igraph_vector_init(i_edge_weights, igraph_ecount(graph)));
            IGRAPH_FINALLY(igraph_vector_destroy, i_edge_weights);
            igraph_vector_fill(i_edge_weights, 1);
        } else {
            if (igraph_vector_size(edge_weights) != ecount) {
                IGRAPH_ERRORF("Edge weight vector length (%" IGRAPH_PRId ") does not match number of edges (%" IGRAPH_PRId ").",
                              IGRAPH_EINVAL, igraph_vector_size(edge_weights), ecount);
            }
            i_edge_weights = (igraph_vector_t*)edge_weights;
        }

        /* Check vertex out-weights to possibly use default. */
        if (!vertex_out_weights) {
            i_vertex_out_weights = IGRAPH_CALLOC(1, igraph_vector_t);
            IGRAPH_CHECK_OOM(i_vertex_out_weights, "Leiden algorithm failed, could not allocate memory for vertex weights.");
            IGRAPH_FINALLY(igraph_free, i_vertex_out_weights);
            IGRAPH_VECTOR_INIT_FINALLY(i_vertex_out_weights, vcount);
            igraph_vector_fill(i_vertex_out_weights, 1);
        } else {
            if (igraph_vector_size(vertex_out_weights) != vcount) {
                IGRAPH_ERRORF("Vertex %sweight vector length (%" IGRAPH_PRId ") does not match number of vertices (%" IGRAPH_PRId ").",
                              IGRAPH_EINVAL,
                              directed ? "out-" : "",
                              igraph_vector_size(vertex_out_weights), vcount);
            }
            i_vertex_out_weights = (igraph_vector_t*)vertex_out_weights;
        }

        if (directed) {
            if (vertex_in_weights) {
                if (igraph_vector_size(vertex_in_weights) != vcount) {
                    IGRAPH_ERRORF("Vertex in-weight vector length (%" IGRAPH_PRId ") does not match number of vertices (%" IGRAPH_PRId ").",
                                  IGRAPH_EINVAL,
                                  igraph_vector_size(vertex_in_weights), vcount);
                }
                i_vertex_in_weights = (igraph_vector_t*)vertex_in_weights;
            } else {
                i_vertex_in_weights = i_vertex_out_weights;
            }
        } else {
            if (vertex_in_weights) {
                IGRAPH_ERROR("Vertex in-weights must not be given for undirected graphs.", IGRAPH_EINVAL);
            } else {
                i_vertex_in_weights = NULL;
            }
        }

        igraph_bool_t changed = true;
        for (igraph_int_t itr = 0;
             n_iterations < 0 ? changed : itr < n_iterations;
             itr++) {
            IGRAPH_CHECK(community_leiden(graph,
                                          i_edge_weights, i_vertex_out_weights, i_vertex_in_weights,
                                          resolution, beta, allow_isolation, only_local_moving,
                                          mem, nb_clusters, quality, &changed));
        }

        if (memberships) {
            IGRAPH_CHECK(igraph_vector_int_list_resize(memberships, vcount));
            for (igraph_int_t v = 0; v < vcount; v++) {
                igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
                IGRAPH_CHECK(igraph_vector_int_resize(sigma, 1));
                VECTOR(*sigma)[0] = VECTOR(*mem)[v];
            }
        }

        if (!edge_weights) {
            igraph_vector_destroy(i_edge_weights);
            IGRAPH_FREE(i_edge_weights);
            IGRAPH_FINALLY_CLEAN(2);
        }

        if (!vertex_out_weights) {
            igraph_vector_destroy(i_vertex_out_weights);
            IGRAPH_FREE(i_vertex_out_weights);
            IGRAPH_FINALLY_CLEAN(2);
        }

        if (use_temp) {
            igraph_vector_int_destroy(&mem_temp);
            IGRAPH_FINALLY_CLEAN(1);
        }

        return IGRAPH_SUCCESS;
    } else {
        /* Overlapping path: max_memberships > 1. Undirected only. */
        if (directed) {
            IGRAPH_ERROR("Overlapping Leiden algorithm is only implemented for undirected graphs.", IGRAPH_EINVAL);
        }
        IGRAPH_UNUSED(membership);
        return igraph_i_community_leiden_run_overlapping(
                   graph, edge_weights, vertex_out_weights,
                   resolution, beta, max_memberships, start, n_iterations,
                   allow_isolation, only_local_moving,
                   memberships, nb_clusters, quality);
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
    const igraph_int_t ecount = igraph_ecount(graph);
    const igraph_bool_t directed = igraph_is_directed(graph);
    igraph_vector_t vertex_out_weights, vertex_in_weights;
    igraph_vector_int_t i_membership, *p_membership;
    igraph_real_t min_weight = IGRAPH_INFINITY;

    /* Basic weight vector validation, calculate properties used for validation steps
     * specific to different objective functions. */
    if (weights) {
        if (igraph_vector_size(weights) != ecount) {
            IGRAPH_ERROR("Edge weight vector length does not match number of edges.", IGRAPH_EINVAL);
        }
        for (igraph_int_t i=0; i < ecount; i++) {
            igraph_real_t w = VECTOR(*weights)[i];
            if (w < min_weight) {
                min_weight = w;
            }
            if (! isfinite(w)) {
                IGRAPH_ERRORF("Edge weights must not be infinite or NaN, got %g.",
                              IGRAPH_EINVAL, w);
            }
        }
    }

    IGRAPH_VECTOR_INIT_FINALLY(&vertex_out_weights, vcount);
    if (directed) {
        IGRAPH_VECTOR_INIT_FINALLY(&vertex_in_weights, vcount);
    }

    /* igraph_community_leiden() always requires an initialized membership vector
     * of the correct size to be given. We relax this requirement to the case
     * when start = true. */
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
        p_membership = membership;
    } else {
        if (!membership) {
            IGRAPH_VECTOR_INT_INIT_FINALLY(&i_membership, vcount);
            p_membership = &i_membership;
        } else {
            IGRAPH_CHECK(igraph_vector_int_resize(membership, vcount));
            p_membership = membership;
        }
    }

    switch (objective) {
    case IGRAPH_LEIDEN_OBJECTIVE_MODULARITY:
        if (min_weight < 0) {
            IGRAPH_ERRORF("Edge weights must not be negative for Leiden community "
                          "detection with modularity objective function, got %g.",
                          IGRAPH_EINVAL,
                          min_weight);
        }

        IGRAPH_CHECK(igraph_strength(
            graph, &vertex_out_weights,
            igraph_vss_all(), IGRAPH_OUT, IGRAPH_LOOPS, weights));
        if (directed) {
            IGRAPH_CHECK(igraph_strength(
                graph, &vertex_in_weights,
                igraph_vss_all(), IGRAPH_IN, IGRAPH_LOOPS, weights));
        }

        /* If directed, the sum of vertex_out_weights is the total edge weight.
         * If undirected, it is twice the total edge weight. */
        resolution /= igraph_vector_sum(&vertex_out_weights);

        break;

    case IGRAPH_LEIDEN_OBJECTIVE_CPM:
        /* TODO: Potential minor optimization is to use the same vector for both. */
        igraph_vector_fill(&vertex_out_weights, 1);
        if (directed) {
            igraph_vector_fill(&vertex_in_weights, 1);
        }

        break;

    case IGRAPH_LEIDEN_OBJECTIVE_ER:
        if (min_weight < 0) {
            IGRAPH_ERRORF("Edge weights must not be negative for Leiden community "
                          "detection with ER objective function, got %g.",
                          IGRAPH_EINVAL,
                          min_weight);
        }

        /* TODO: Potential minor optimization is to use the same vector for both. */
        igraph_vector_fill(&vertex_out_weights, 1);
        if (directed) {
            igraph_vector_fill(&vertex_in_weights, 1);
        }

        {
            igraph_real_t p;
            /* Note: Loops must be allowed, as the aggregation step of the
             * algorithm effectively creates them. */
            IGRAPH_CHECK(igraph_density(graph, weights, &p, /* loops */ true));
            resolution *= p;
        }

        break;


    default:
        IGRAPH_ERROR("Invalid objective function for Leiden community detection.",
                     IGRAPH_EINVAL);
    }

    IGRAPH_CHECK(igraph_community_leiden(
        graph, weights,
        &vertex_out_weights, directed ? &vertex_in_weights : NULL,
        resolution, beta,
        /*max_memberships=*/ 1, start, n_iterations,
        /*allow_isolation=*/ true, /*only_local_moving=*/ false,
        p_membership, /*memberships=*/ NULL, nb_clusters, quality));

    if (!membership) {
        igraph_vector_int_destroy(&i_membership);
        IGRAPH_FINALLY_CLEAN(1);
    }

    if (directed) {
        igraph_vector_destroy(&vertex_in_weights);
        IGRAPH_FINALLY_CLEAN(1);
    }
    igraph_vector_destroy(&vertex_out_weights);
    IGRAPH_FINALLY_CLEAN(1);

    return IGRAPH_SUCCESS;
}
/*
 *
 * This section extends the Leiden algorithm above from disjoint partitions
 * to overlapping covers, following the exact-potential-game formulation of
 * the CPM established in "From Leiden to Pleasure Island". Each node v now
 * holds a *membership vector* (a set of community IDs), and the local
 * moving phase evaluates three unilateral action types: ADD a community to
 * the vector, REMOVE one from it, or SUBSTITUTE one for another.
 *
 * --- The quality function (mitigation of edge double-counting) ---
 *
 * Node v with k_v = |sigma_v| memberships participates in community c with
 * fractional intensity f_v^c = 1 / sqrt(k_v). The global quality is
 *
 *   Q(pi) = sum_c [ E_c - (gamma/2) S_c^2 ],
 *     E_c = sum_{i<j} A_ij f_i^c f_j^c,   S_c = sum_i n_i f_i^c.
 *
 * The pairwise interaction coefficient is therefore
 *
 *   kappa_ij = |sigma_i INTERSECT sigma_j| / sqrt(k_i k_j)  <=  1
 *
 * by Cauchy-Schwarz, with equality iff sigma_i == sigma_j. Hence a pair of
 * nodes can never contribute more than the original CPM pair value
 * (A_ij - gamma n_i n_j): edges are *never* double-counted, and on a
 * disjoint cover (all k = 1) Q reduces exactly to the CPM quality
 * optimized by igraph_community_leiden() above (S_c^2 mirrors the N_c^2
 * convention used there, so self-pair terms cancel identically in all
 * move comparisons because sum_{c in sigma_v} (n_v f_v^c)^2 = n_v^2 is a
 * constant independent of the membership vector).
 *
 * Why the L2 normalization 1/sqrt(k) instead of the L1 dilution 1/k?
 * Under L1, a node's total contribution to Q is the *mean* of its
 * per-community alignment values, and a mean is always maximized by the
 * single best element: every best response collapses to one membership and
 * the model provably degenerates to the disjoint case. L2 is the minimal
 * concavification that (a) keeps kappa <= 1, (b) preserves the exact
 * reduction to CPM on disjoint covers, and (c) admits strictly profitable
 * overlap: a second membership pays iff its alignment value exceeds
 * (sqrt(2)-1) times the first, a structural entry hurdle.
 *
 * --- Exact potential game (mitigation of convergence loss) ---
 *
 * The utility of node v is its marginal contribution to Q. With
 *
 *   g_c(v) = L_v^c - gamma n_v W_v^c,
 *     L_v^c = sum_{u ~ v} A_uv f_u^c  (fractional edge weight to c),
 *     W_v^c = S_c - n_v f_v^c        (fractional mass of c excluding v),
 *
 * the contribution of v under membership set sigma is, up to the constant
 * gamma n_v^2 / 2 self-term,
 *
 *   U_v(sigma) = ( sum_{c in sigma} g_c(v) ) / sqrt(|sigma|),
 *
 * and Delta U = Delta Q holds *identically* for every unilateral ADD,
 * REMOVE or SUBSTITUTE: Phi(pi) = Q(pi) is an exact potential. Every
 * executed action strictly increases the bounded potential Phi, so the
 * typed action metagraph (append / revoke / substitution edges over the
 * cover space) is a DAG graded by Phi and no cycles are possible; play
 * terminates in a pure Nash equilibrium of the overlapping hedonic game.
 * With a rational resolution gamma = b/c^ and the finite value set
 * {1/sqrt(j) : j <= K}, per-move gains live in a finite lattice bounded
 * away from zero, giving the pseudo-polynomial convergence of Theorem 1
 * scaled by K^2 (K = max_memberships). All comparisons are linear in
 * gamma, so the interval-stability machinery of Theorems 4 and 5 lifts
 * verbatim: a membership vector that is a best response at gamma_0 and at
 * gamma_1 is a best response on all of [gamma_0, gamma_1], and the
 * generalized familiarity threshold of an action with edge-gain Delta L
 * and mass-gain Delta W is gamma* = Delta L / (n_v Delta W): the
 * resolution at which that branch of the decision tree flips from a clear
 * choice to a frustrated one.
 *
 * --- Membership proliferation (mitigation of explosion) ---
 *
 * Three coupled brakes prevent membership explosion:
 *  1. Dilution: adding community c rescales *all* of v's intensities from
 *     1/sqrt(k) to 1/sqrt(k+1), so entry is profitable only if
 *     g_c > (sqrt((k+1)/k) - 1) * sum of current g values -- a hurdle that
 *     grows with the quality of the portfolio already held.
 *  2. Density: g_c itself charges gamma n_v W_v^c against *the entire
 *     fractional mass* of the candidate community; sparse or ill-fitting
 *     communities have negative g and are never entered.
 *  3. A hard cap K = max_memberships bounds the vector length and the
 *     convergence constant.
 *
 * --- The three-branch decision tree ---
 *
 * Because g_c(v) does not depend on v's own vector, the per-visit decision
 * problem "choose the best sigma' among all ADD/REMOVE/SUBSTITUTE
 * combinations" has a closed-form solution: sort candidate communities by
 * g descending and pick the prefix of length j <= K maximizing
 * (prefix sum) / sqrt(j). ADD corresponds to extending the prefix, REMOVE
 * to shrinking it, SUBSTITUTE to exchanging its boundary element; a fresh
 * empty community (g = 0) is always among the candidates, subsuming
 * isolation moves. This computes the exact best response in
 * O(deg(v) K + C log C) per visit.
 *
 * --- Phases 2 and 3 on the token graph ---
 *
 * After the overlapping local-moving phase converges, each (node,
 * community) pair becomes a *token* with node weight n_v / sqrt(k_v), and
 * each edge (u, v) of the original graph induces token edges with weight
 * A_uv f_u f_v. With the k's frozen, Q restricted to token relabelings is
 * *exactly* the disjoint CPM on this token graph, so the original
 * refinement (igraph_i_community_leiden_mergenodes) and aggregation
 * (igraph_i_community_leiden_aggregate) machinery -- and the entire
 * multi-level loop -- are reused unchanged on tokens. Meta-nodes inherit
 * membership-vector slices as groups of tokens and move as units, which
 * keeps Delta Phi exact at every aggregation level. The one relaxation:
 * higher-level merges may land two tokens of the same node in the same
 * community; such duplicates are collapsed when projecting back
 * (multiset -> set), the node is re-examined by the next overlapping
 * phase, and the outer driver only continues while the overlapping
 * quality Q strictly improves, so the wrapper cannot cycle.
 */

typedef struct {
    igraph_real_t gain;       /* g_c = L_v^c - gamma * n_v * W_v^c */
    igraph_integer_t comm;
} igraph_i_leiden_ov_cand_t;

/* Sort candidates by gain, descending; break ties on community ID so the
 * best response is deterministic for a given RNG state. */
static int igraph_i_leiden_ov_cand_cmp(const void *a, const void *b) {
    const igraph_i_leiden_ov_cand_t *ca = (const igraph_i_leiden_ov_cand_t *) a;
    const igraph_i_leiden_ov_cand_t *cb = (const igraph_i_leiden_ov_cand_t *) b;
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

/* Grow the community-indexed bookkeeping arrays so that community IDs up
 * to needed - 1 are addressable. New entries represent empty communities
 * and are zeroed. */
static igraph_error_t igraph_i_leiden_ov_ensure_cap(
        const igraph_integer_t needed,
        igraph_integer_t *cap,
        igraph_vector_t *comm_mass,
        igraph_vector_int_t *comm_tokens,
        igraph_vector_t *edge_w_to_comm,
        igraph_vector_int_t *comm_seen) {
    igraph_integer_t newcap;

    if (needed <= *cap) {
        return IGRAPH_SUCCESS;
    }
    newcap = 2 * (*cap);
    if (newcap < needed) {
        newcap = needed;
    }
    IGRAPH_CHECK(igraph_vector_resize(comm_mass, newcap));
    IGRAPH_CHECK(igraph_vector_int_resize(comm_tokens, newcap));
    IGRAPH_CHECK(igraph_vector_resize(edge_w_to_comm, newcap));
    IGRAPH_CHECK(igraph_vector_int_resize(comm_seen, newcap));
    for (igraph_integer_t c = *cap; c < newcap; c++) {
        VECTOR(*comm_mass)[c] = 0.0;
        VECTOR(*comm_tokens)[c] = 0;
        VECTOR(*edge_w_to_comm)[c] = 0.0;
        VECTOR(*comm_seen)[c] = 0;
    }
    *cap = newcap;

    return IGRAPH_SUCCESS;
}

/* Overlapping local moving phase (Phase 1).
 *
 * Queue-driven like igraph_i_community_leiden_fastmovenodes, but each
 * visit computes the node's exact best-response membership *set* instead
 * of a single best cluster: candidate communities (the node's own, its
 * neighbours', plus -- when \p allow_isolation is true -- one recyclable
 * empty community) are scored by g_c = L_v^c - gamma n_v W_v^c and the
 * prefix of the descending-sorted candidates maximizing (sum g) /
 * sqrt(j), j <= max_memberships, is adopted whenever it strictly beats
 * the current score. Every adopted change strictly increases the exact
 * potential Phi = Q, which is what rules out cycles (DAG metagraph) and
 * bounds the number of moves.
 *
 * When \p allow_isolation is false, the empty-community candidate is
 * withheld, so a node can only add, remove or substitute memberships
 * among communities that are already non-empty; this mirrors the
 * \c allow_isolation parameter of igraph_i_community_leiden_fastmovenodes.
 *
 * Membership vectors in \c memberships must be sorted, duplicate-free and
 * non-empty; they are updated in place and remain so.
 */
static igraph_error_t igraph_i_community_leiden_ov_fastmovenodes(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_node,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *node_weights,
        const igraph_real_t resolution_parameter,
        const igraph_bool_t *allow_isolation,
        const igraph_integer_t max_memberships,
        igraph_vector_int_list_t *memberships,
        igraph_bool_t *changed) {

    const igraph_integer_t n = igraph_vcount(graph);
    igraph_dqueue_int_t unstable_nodes;
    igraph_bitset_t node_is_stable;
    igraph_vector_int_t node_order;
    igraph_stack_int_t empty_comms;
    igraph_vector_t comm_mass;         /* S_c, fractional mass per community */
    igraph_vector_int_t comm_tokens;   /* number of member tokens per community */
    igraph_vector_t edge_w_to_comm;    /* L_v^c scratch, zeroed after each visit */
    igraph_vector_int_t comm_seen;     /* candidate-collection flags, ditto */
    igraph_vector_t inv_sqrt;          /* 1/sqrt(j) for j = 1..max_memberships */
    igraph_vector_int_t chosen;
    igraph_i_leiden_ov_cand_t *cand;
    igraph_integer_t cap = 1, nb_comm_ids = 0, maxdeg = 0, cand_cap;
    int iter = 0;

    /* Number of community IDs in use; membership vectors are assumed
     * compact (IDs 0..nb_comm_ids-1, every ID non-empty). */
    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        igraph_integer_t degree = igraph_vector_int_size(igraph_inclist_get(edges_per_node, v));
        if (k < 1 || k > max_memberships) {
            IGRAPH_ERROR("Invalid overlapping membership vector size.", IGRAPH_EINVAL);
        }
        if (degree > maxdeg) {
            maxdeg = degree;
        }
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            if (VECTOR(*sigma)[idx] + 1 > nb_comm_ids) {
                nb_comm_ids = VECTOR(*sigma)[idx] + 1;
            }
        }
    }
    if (nb_comm_ids + 1 > cap) {
        cap = nb_comm_ids + 1;
    }

    IGRAPH_VECTOR_INIT_FINALLY(&comm_mass, cap);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&comm_tokens, cap);
    IGRAPH_VECTOR_INIT_FINALLY(&edge_w_to_comm, cap);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&comm_seen, cap);

    IGRAPH_VECTOR_INIT_FINALLY(&inv_sqrt, max_memberships + 1);
    for (igraph_integer_t j = 1; j <= max_memberships; j++) {
        VECTOR(inv_sqrt)[j] = 1.0 / sqrt((igraph_real_t) j);
    }

    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        igraph_real_t fv = VECTOR(inv_sqrt)[k];
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            igraph_integer_t c = VECTOR(*sigma)[idx];
            VECTOR(comm_mass)[c] += VECTOR(*node_weights)[v] * fv;
            VECTOR(comm_tokens)[c] += 1;
        }
    }

    IGRAPH_STACK_INT_INIT_FINALLY(&empty_comms, 8);

    IGRAPH_BITSET_INIT_FINALLY(&node_is_stable, n);
    IGRAPH_DQUEUE_INT_INIT_FINALLY(&unstable_nodes, n);

    IGRAPH_CHECK(igraph_vector_int_init_range(&node_order, 0, n));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &node_order);
    igraph_vector_int_shuffle(&node_order);
    for (igraph_integer_t i = 0; i < n; i++) {
        IGRAPH_CHECK(igraph_dqueue_int_push(&unstable_nodes, VECTOR(node_order)[i]));
    }

    IGRAPH_VECTOR_INT_INIT_FINALLY(&chosen, max_memberships);

    /* Candidates per visit: v's own <= K, at most deg * K from neighbours,
     * plus one empty community. */
    cand_cap = maxdeg * max_memberships + max_memberships + 1;
    cand = IGRAPH_CALLOC(cand_cap, igraph_i_leiden_ov_cand_t);
    IGRAPH_CHECK_OOM(cand, "Insufficient memory for overlapping Leiden.");
    IGRAPH_FINALLY(igraph_free, cand);

    while (!igraph_dqueue_int_empty(&unstable_nodes)) {
        igraph_integer_t v = igraph_dqueue_int_pop(&unstable_nodes);
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        igraph_real_t nv = VECTOR(*node_weights)[v];
        igraph_real_t fv = VECTOR(inv_sqrt)[k];
        igraph_vector_int_t *edges;
        igraph_integer_t degree, ncand = 0, empty_c = -1, best_j = 0, jmax;
        igraph_real_t cur_score = 0.0, best_score, prefix;

        /* Keep one recyclable empty community available as a candidate,
         * unless isolation moves are disallowed; this subsumes isolation
         * moves (their gain is exactly 0). empty_c stays -1, a value no
         * real community ID ever takes, when allow_isolation is false. */
        if (*allow_isolation) {
            if (igraph_stack_int_empty(&empty_comms)) {
                IGRAPH_CHECK(igraph_i_leiden_ov_ensure_cap(nb_comm_ids + 1, &cap,
                             &comm_mass, &comm_tokens, &edge_w_to_comm, &comm_seen));
                IGRAPH_CHECK(igraph_stack_int_push(&empty_comms, nb_comm_ids));
                nb_comm_ids++;
            }
            empty_c = igraph_stack_int_top(&empty_comms);
        }

        /* Candidates: v's own communities first (indices 0..k-1; this
         * ordering is relied upon for the W_c correction below). */
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            igraph_integer_t c = VECTOR(*sigma)[idx];
            VECTOR(comm_seen)[c] = 1;
            cand[ncand].comm = c;
            ncand++;
        }

        /* Accumulate fractional edge weights L_v^c and collect the
         * neighbouring communities as candidates. */
        edges = igraph_inclist_get(edges_per_node, v);
        degree = igraph_vector_int_size(edges);
        for (igraph_integer_t i = 0; i < degree; i++) {
            igraph_integer_t e = VECTOR(*edges)[i];
            igraph_integer_t u = IGRAPH_OTHER(graph, e, v);
            igraph_vector_int_t *sigma_u;
            igraph_integer_t ku;
            igraph_real_t wf;
            if (u == v) {
                continue;
            }
            sigma_u = igraph_vector_int_list_get_ptr(memberships, u);
            ku = igraph_vector_int_size(sigma_u);
            wf = VECTOR(*edge_weights)[e] * VECTOR(inv_sqrt)[ku];
            for (igraph_integer_t idx = 0; idx < ku; idx++) {
                igraph_integer_t c = VECTOR(*sigma_u)[idx];
                if (!VECTOR(comm_seen)[c]) {
                    VECTOR(comm_seen)[c] = 1;
                    cand[ncand].comm = c;
                    ncand++;
                }
                VECTOR(edge_w_to_comm)[c] += wf;
            }
        }

        if (empty_c >= 0 && !VECTOR(comm_seen)[empty_c]) {
            VECTOR(comm_seen)[empty_c] = 1;
            cand[ncand].comm = empty_c;
            ncand++;
        }

        /* Gains g_c = L_v^c - gamma n_v W_v^c, where W_v^c excludes v's own
         * mass; clear the scratch arrays along the way. */
        for (igraph_integer_t i = 0; i < ncand; i++) {
            igraph_integer_t c = cand[i].comm;
            cand[i].gain = VECTOR(edge_w_to_comm)[c]
                           - resolution_parameter * nv * VECTOR(comm_mass)[c];
            VECTOR(edge_w_to_comm)[c] = 0.0;
            VECTOR(comm_seen)[c] = 0;
        }
        /* The first k candidates are v's current communities, whose mass
         * still includes v's token: add it back. The current score is v's
         * actual contribution to Q (up to the constant self-term). */
        for (igraph_integer_t i = 0; i < k; i++) {
            cand[i].gain += resolution_parameter * nv * nv * fv;
            cur_score += cand[i].gain;
        }
        cur_score *= fv;

        qsort(cand, (size_t) ncand, sizeof(*cand), igraph_i_leiden_ov_cand_cmp);

        /* Exact best response: the prefix of length j maximizing
         * (sum of top-j gains) / sqrt(j). Extending the prefix is the ADD
         * branch, shrinking it the REMOVE branch, exchanging its boundary
         * the SUBSTITUTE branch of the decision tree. Only strict
         * improvements are adopted (essential for convergence). */
        best_score = cur_score;
        prefix = 0.0;
        jmax = ncand < max_memberships ? ncand : max_memberships;
        for (igraph_integer_t j = 1; j <= jmax; j++) {
            igraph_real_t score;
            prefix += cand[j - 1].gain;
            score = prefix * VECTOR(inv_sqrt)[j];
            if (score > best_score) {
                best_score = score;
                best_j = j;
            }
        }

        if (best_j > 0) {
            igraph_bool_t same;
            igraph_real_t fnew = VECTOR(inv_sqrt)[best_j];
            igraph_bool_t used_empty = false;
            igraph_integer_t ia = 0, ib = 0;

            IGRAPH_CHECK(igraph_vector_int_resize(&chosen, best_j));
            for (igraph_integer_t j = 0; j < best_j; j++) {
                VECTOR(chosen)[j] = cand[j].comm;
                if (cand[j].comm == empty_c) {
                    used_empty = true;
                }
            }
            igraph_vector_int_sort(&chosen);

            /* Guard against no-op "moves" caused by floating point
             * summation-order differences between cur_score and the
             * prefix sums. */
            same = (best_j == k);
            if (same) {
                for (igraph_integer_t j = 0; j < best_j; j++) {
                    if (VECTOR(chosen)[j] != VECTOR(*sigma)[j]) {
                        same = false;
                        break;
                    }
                }
            }

            if (!same) {
                *changed = true;

                /* Pop the empty community before any push can bury it. */
                if (used_empty) {
                    igraph_stack_int_pop(&empty_comms);
                }

                /* Classify communities by merging the two sorted sets and
                 * update the fractional masses: removed ones lose n_v f_old,
                 * added ones gain n_v f_new, retained ones are rescaled. */
                while (ia < k || ib < best_j) {
                    if (ib >= best_j ||
                        (ia < k && VECTOR(*sigma)[ia] < VECTOR(chosen)[ib])) {
                        igraph_integer_t c = VECTOR(*sigma)[ia++];
                        VECTOR(comm_mass)[c] -= nv * fv;
                        VECTOR(comm_tokens)[c] -= 1;
                        if (VECTOR(comm_tokens)[c] == 0) {
                            VECTOR(comm_mass)[c] = 0.0;
                            IGRAPH_CHECK(igraph_stack_int_push(&empty_comms, c));
                        }
                    } else if (ia >= k ||
                               VECTOR(chosen)[ib] < VECTOR(*sigma)[ia]) {
                        igraph_integer_t c = VECTOR(chosen)[ib++];
                        VECTOR(comm_mass)[c] += nv * fnew;
                        VECTOR(comm_tokens)[c] += 1;
                    } else {
                        igraph_integer_t c = VECTOR(*sigma)[ia];
                        VECTOR(comm_mass)[c] += nv * (fnew - fv);
                        ia++;
                        ib++;
                    }
                }
                IGRAPH_CHECK(igraph_vector_int_update(sigma, &chosen));

                /* A changed vector can alter the best response of any
                 * neighbour; re-queue the stable ones. */
                for (igraph_integer_t i = 0; i < degree; i++) {
                    igraph_integer_t e = VECTOR(*edges)[i];
                    igraph_integer_t u = IGRAPH_OTHER(graph, e, v);
                    if (u != v && IGRAPH_BIT_TEST(node_is_stable, u)) {
                        IGRAPH_CHECK(igraph_dqueue_int_push(&unstable_nodes, u));
                        IGRAPH_BIT_CLEAR(node_is_stable, u);
                    }
                }
            }
        }

        IGRAPH_BIT_SET(node_is_stable, v);

        IGRAPH_ALLOW_INTERRUPTION_LIMITED(iter, 1 << 13);
    }

    IGRAPH_FREE(cand);
    igraph_vector_int_destroy(&chosen);
    igraph_vector_int_destroy(&node_order);
    igraph_dqueue_int_destroy(&unstable_nodes);
    igraph_bitset_destroy(&node_is_stable);
    igraph_stack_int_destroy(&empty_comms);
    igraph_vector_destroy(&inv_sqrt);
    igraph_vector_int_destroy(&comm_seen);
    igraph_vector_destroy(&edge_w_to_comm);
    igraph_vector_int_destroy(&comm_tokens);
    igraph_vector_destroy(&comm_mass);
    IGRAPH_FINALLY_CLEAN(11);

    return IGRAPH_SUCCESS;
}

/* Renumber community IDs consecutively from 0 in order of first appearance
 * and keep each membership vector sorted. Returns the number of distinct
 * communities in nb_clusters. */
static igraph_error_t igraph_i_community_leiden_ov_compact(
        igraph_vector_int_list_t *memberships,
        igraph_integer_t *nb_clusters) {
    const igraph_integer_t n = igraph_vector_int_list_size(memberships);
    igraph_integer_t maxid = -1, next = 0;
    igraph_vector_int_t new_id;

    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            if (VECTOR(*sigma)[idx] > maxid) {
                maxid = VECTOR(*sigma)[idx];
            }
        }
    }

    IGRAPH_VECTOR_INT_INIT_FINALLY(&new_id, maxid + 1);
    igraph_vector_int_fill(&new_id, -1);

    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            igraph_integer_t c = VECTOR(*sigma)[idx];
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

/* Overlapping quality
 *
 *   Q = (1/2m) sum_c ( 2 E_c - gamma S_c^2 )
 *
 * with E_c and S_c as in the section comment. Reduces exactly to the
 * quality of igraph_i_community_leiden_quality on disjoint covers.
 * Self-loops contribute their full weight independently of the membership
 * vectors (sum_c (f_v^c)^2 = 1), mirroring their neutral role above. */
static igraph_error_t igraph_i_community_leiden_ov_quality(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *node_weights,
        igraph_vector_int_list_t *memberships,
        const igraph_real_t resolution_parameter,
        igraph_real_t *quality) {
    const igraph_integer_t n = igraph_vcount(graph);
    const igraph_integer_t m = igraph_ecount(graph);
    igraph_real_t total_edge_weight = 0.0, q = 0.0;
    igraph_vector_t comm_mass;
    igraph_integer_t maxid = -1;

    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            if (VECTOR(*sigma)[idx] > maxid) {
                maxid = VECTOR(*sigma)[idx];
            }
        }
    }

    IGRAPH_VECTOR_INIT_FINALLY(&comm_mass, maxid + 1);
    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        igraph_real_t fv = 1.0 / sqrt((igraph_real_t) k);
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            VECTOR(comm_mass)[VECTOR(*sigma)[idx]] += VECTOR(*node_weights)[v] * fv;
        }
    }

    for (igraph_integer_t e = 0; e < m; e++) {
        igraph_integer_t from = IGRAPH_FROM(graph, e), to = IGRAPH_TO(graph, e);
        igraph_real_t w = VECTOR(*edge_weights)[e];
        igraph_vector_int_t *sig_f, *sig_t;
        igraph_integer_t kf, kt, ia = 0, ib = 0, shared = 0;

        total_edge_weight += w;
        if (from == to) {
            q += 2 * w;
            continue;
        }
        sig_f = igraph_vector_int_list_get_ptr(memberships, from);
        sig_t = igraph_vector_int_list_get_ptr(memberships, to);
        kf = igraph_vector_int_size(sig_f);
        kt = igraph_vector_int_size(sig_t);
        while (ia < kf && ib < kt) {
            if (VECTOR(*sig_f)[ia] < VECTOR(*sig_t)[ib]) {
                ia++;
            } else if (VECTOR(*sig_f)[ia] > VECTOR(*sig_t)[ib]) {
                ib++;
            } else {
                shared++;
                ia++;
                ib++;
            }
        }
        if (shared > 0) {
            q += 2 * w * shared / sqrt((igraph_real_t) (kf * kt));
        }
    }

    for (igraph_integer_t c = 0; c <= maxid; c++) {
        q -= resolution_parameter * VECTOR(comm_mass)[c] * VECTOR(comm_mass)[c];
    }

    igraph_vector_destroy(&comm_mass);
    IGRAPH_FINALLY_CLEAN(1);

    if (total_edge_weight > 0) {
        q /= 2.0 * total_edge_weight;
    }
    *quality = q;

    return IGRAPH_SUCCESS;
}

/* Build the token graph: one vertex per (node, community) membership
 * token, with node weight n_v / sqrt(k_v), and one edge per (original
 * edge, token pair) combination with weight A_uv f_u f_v. With the
 * membership-vector lengths frozen, the disjoint CPM on this graph equals
 * the overlapping quality Q, which is what lets the original refinement
 * and aggregation machinery run unchanged on top of it. Self-loops are
 * skipped: their contribution to Q is membership-independent.
 *
 * token_graph is created here (uninitialized on entry); the remaining
 * output vectors must be initialized. */
static igraph_error_t igraph_i_community_leiden_ov_tokens(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights,
        const igraph_vector_t *node_weights,
        igraph_vector_int_list_t *memberships,
        igraph_t *token_graph,
        igraph_vector_t *token_edge_weights,
        igraph_vector_t *token_node_weights,
        igraph_vector_int_t *token_membership,
        igraph_vector_int_t *token_offset) {
    const igraph_integer_t n = igraph_vcount(graph);
    const igraph_integer_t m = igraph_ecount(graph);
    igraph_vector_int_t token_edges;
    igraph_integer_t nb_tokens = 0;

    IGRAPH_CHECK(igraph_vector_int_resize(token_offset, n + 1));
    for (igraph_integer_t v = 0; v < n; v++) {
        VECTOR(*token_offset)[v] = nb_tokens;
        nb_tokens += igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, v));
    }
    VECTOR(*token_offset)[n] = nb_tokens;

    IGRAPH_CHECK(igraph_vector_resize(token_node_weights, nb_tokens));
    IGRAPH_CHECK(igraph_vector_int_resize(token_membership, nb_tokens));
    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        igraph_real_t fv = 1.0 / sqrt((igraph_real_t) k);
        for (igraph_integer_t idx = 0; idx < k; idx++) {
            igraph_integer_t t = VECTOR(*token_offset)[v] + idx;
            VECTOR(*token_node_weights)[t] = VECTOR(*node_weights)[v] * fv;
            VECTOR(*token_membership)[t] = VECTOR(*sigma)[idx];
        }
    }

    IGRAPH_VECTOR_INT_INIT_FINALLY(&token_edges, 0);
    igraph_vector_clear(token_edge_weights);

    for (igraph_integer_t e = 0; e < m; e++) {
        igraph_integer_t from = IGRAPH_FROM(graph, e), to = IGRAPH_TO(graph, e);
        igraph_integer_t kf, kt;
        igraph_real_t wff;
        if (from == to) {
            continue;
        }
        kf = igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, from));
        kt = igraph_vector_int_size(igraph_vector_int_list_get_ptr(memberships, to));
        wff = VECTOR(*edge_weights)[e] / sqrt((igraph_real_t) (kf * kt));
        for (igraph_integer_t i = 0; i < kf; i++) {
            for (igraph_integer_t j = 0; j < kt; j++) {
                IGRAPH_CHECK(igraph_vector_int_push_back(&token_edges, VECTOR(*token_offset)[from] + i));
                IGRAPH_CHECK(igraph_vector_int_push_back(&token_edges, VECTOR(*token_offset)[to] + j));
                IGRAPH_CHECK(igraph_vector_push_back(token_edge_weights, wff));
            }
        }
    }

    IGRAPH_CHECK(igraph_create(token_graph, &token_edges, nb_tokens, IGRAPH_UNDIRECTED));

    igraph_vector_int_destroy(&token_edges);
    IGRAPH_FINALLY_CLEAN(1);

    return IGRAPH_SUCCESS;
}

/* Project the final token clustering back onto per-node membership
 * vectors. Duplicate labels (two tokens of the same node ending up in the
 * same community after aggregation-level merges) are collapsed
 * multiset -> set; deduped reports whether that happened, since those
 * nodes must be re-examined by the next overlapping phase. */
static igraph_error_t igraph_i_community_leiden_ov_project(
        const igraph_vector_int_t *token_membership,
        const igraph_vector_int_t *token_offset,
        igraph_vector_int_list_t *memberships,
        igraph_bool_t *deduped) {
    const igraph_integer_t n = igraph_vector_int_list_size(memberships);
    igraph_vector_int_t labels;

    IGRAPH_VECTOR_INT_INIT_FINALLY(&labels, 0);
    *deduped = false;

    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t start = VECTOR(*token_offset)[v];
        igraph_integer_t kt = VECTOR(*token_offset)[v + 1] - start;
        igraph_integer_t distinct = 0;

        IGRAPH_CHECK(igraph_vector_int_resize(&labels, kt));
        for (igraph_integer_t idx = 0; idx < kt; idx++) {
            VECTOR(labels)[idx] = VECTOR(*token_membership)[start + idx];
        }
        igraph_vector_int_sort(&labels);

        IGRAPH_CHECK(igraph_vector_int_resize(sigma, kt));
        for (igraph_integer_t idx = 0; idx < kt; idx++) {
            if (idx == 0 || VECTOR(labels)[idx] != VECTOR(labels)[idx - 1]) {
                VECTOR(*sigma)[distinct] = VECTOR(labels)[idx];
                distinct++;
            }
        }
        if (distinct < kt) {
            *deduped = true;
            IGRAPH_CHECK(igraph_vector_int_resize(sigma, distinct));
        }
    }

    igraph_vector_int_destroy(&labels);
    IGRAPH_FINALLY_CLEAN(1);

    return IGRAPH_SUCCESS;
}

/* One full iteration of the overlapping Leiden algorithm:
 * (1) overlapping local moving on the original graph (exact potential
 *     game over ADD / REMOVE / SUBSTITUTE actions);
 * (2) freeze the membership-vector lengths and materialize the token
 *     graph;
 * (3) run the complete original (disjoint) multi-level Leiden machinery
 *     -- refinement, aggregation and all higher levels -- on the tokens;
 * (4) project the token clustering back to membership vectors, collapsing
 *     duplicates.
 *
 * If \p only_local_moving is true, steps (2)-(4) are skipped entirely and
 * only the overlapping local-moving phase (1) is run, mirroring the
 * \c only_local_moving parameter of igraph_community_leiden(). \p
 * allow_isolation is forwarded to that same phase, controlling whether it
 * may offer a fresh empty community as a candidate membership. */
static igraph_error_t igraph_i_community_leiden_ov_iteration(
        const igraph_t *graph,
        igraph_vector_t *edge_weights,
        igraph_vector_t *node_weights,
        const igraph_real_t resolution_parameter,
        const igraph_real_t beta,
        const igraph_integer_t max_memberships,
        const igraph_bool_t *allow_isolation,
        const igraph_bool_t only_local_moving,
        igraph_vector_int_list_t *memberships,
        igraph_bool_t *changed) {
    igraph_inclist_t edges_per_node;
    igraph_bool_t phase_changed = false, inner_changed = false, dedup_changed = false;
    igraph_bool_t token_allow_isolation = true;
    igraph_integer_t nb_comms, token_nb_clusters;
    igraph_t token_graph;
    igraph_vector_t token_edge_weights, token_node_weights;
    igraph_vector_int_t token_membership, token_offset;

    /* Phase 1: overlapping local moving. */
    IGRAPH_CHECK(igraph_inclist_init(graph, &edges_per_node, IGRAPH_ALL, IGRAPH_LOOPS_TWICE));
    IGRAPH_FINALLY(igraph_inclist_destroy, &edges_per_node);
    IGRAPH_CHECK(igraph_i_community_leiden_ov_fastmovenodes(graph, &edges_per_node,
                 edge_weights, node_weights, resolution_parameter, allow_isolation,
                 max_memberships, memberships, &phase_changed));
    igraph_inclist_destroy(&edges_per_node);
    IGRAPH_FINALLY_CLEAN(1);

    IGRAPH_CHECK(igraph_i_community_leiden_ov_compact(memberships, &nb_comms));

    if (only_local_moving) {
        *changed = phase_changed;
        return IGRAPH_SUCCESS;
    }

    /* Phases 2 and 3 (and all aggregation levels) on the token graph. */
    IGRAPH_VECTOR_INIT_FINALLY(&token_edge_weights, 0);
    IGRAPH_VECTOR_INIT_FINALLY(&token_node_weights, 0);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&token_membership, 0);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&token_offset, 0);

    IGRAPH_CHECK(igraph_i_community_leiden_ov_tokens(graph, edge_weights, node_weights,
                 memberships, &token_graph, &token_edge_weights, &token_node_weights,
                 &token_membership, &token_offset));
    IGRAPH_FINALLY(igraph_destroy, &token_graph);

    /* The disjoint refinement/aggregation machinery always allows
     * isolation on the token graph -- it must stay free to seed new
     * token-level clusters regardless of the caller's overlapping-phase
     * allow_isolation choice above. */
    IGRAPH_CHECK(community_leiden(&token_graph, &token_edge_weights,
                 &token_node_weights, NULL, resolution_parameter, beta,
                 token_allow_isolation, /* only_local_moving = */ false,
                 &token_membership, &token_nb_clusters, /* quality = */ NULL,
                 &inner_changed));

    IGRAPH_CHECK(igraph_i_community_leiden_ov_project(&token_membership, &token_offset,
                 memberships, &dedup_changed));

    igraph_destroy(&token_graph);
    igraph_vector_int_destroy(&token_offset);
    igraph_vector_int_destroy(&token_membership);
    igraph_vector_destroy(&token_node_weights);
    igraph_vector_destroy(&token_edge_weights);
    IGRAPH_FINALLY_CLEAN(5);

    if (phase_changed || inner_changed || dedup_changed) {
        *changed = true;
    }

    return IGRAPH_SUCCESS;
}

/* Validate and clean up a user-supplied initial cover for the overlapping
 * algorithm ("start" mode): every membership vector must be non-empty, its
 * entries must be valid vertex indices, and it must not exceed \p
 * max_memberships once duplicates are removed. Each vector is sorted and
 * deduplicated in place so that it satisfies the invariant relied upon by
 * igraph_i_community_leiden_ov_fastmovenodes. Community IDs themselves are
 * compacted separately by the caller, via
 * igraph_i_community_leiden_ov_compact(). */
static igraph_error_t igraph_i_community_leiden_ov_validate_start(
        const igraph_integer_t n,
        const igraph_integer_t max_memberships,
        igraph_vector_int_list_t *memberships) {
    for (igraph_integer_t v = 0; v < n; v++) {
        igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
        igraph_integer_t k = igraph_vector_int_size(sigma);
        igraph_integer_t distinct;

        if (k < 1) {
            IGRAPH_ERROR("Initial overlapping membership vectors must be non-empty.",
                         IGRAPH_EINVAL);
        }

        igraph_vector_int_sort(sigma);

        distinct = 1;
        for (igraph_integer_t idx = 1; idx < k; idx++) {
            if (VECTOR(*sigma)[idx] != VECTOR(*sigma)[distinct - 1]) {
                VECTOR(*sigma)[distinct] = VECTOR(*sigma)[idx];
                distinct++;
            }
        }
        if (distinct < k) {
            IGRAPH_CHECK(igraph_vector_int_resize(sigma, distinct));
            k = distinct;
        }

        if (k > max_memberships) {
            IGRAPH_ERROR("Initial overlapping membership vector exceeds max_memberships.",
                         IGRAPH_EINVAL);
        }

        if (VECTOR(*sigma)[0] < 0 || VECTOR(*sigma)[k - 1] >= n) {
            IGRAPH_ERROR("Initial overlapping membership indices must be non-negative "
                         "and less than the number of vertices.", IGRAPH_EINVAL);
        }
    }

    return IGRAPH_SUCCESS;
}

/* Full multi-iteration overlapping Leiden (max_memberships > 1 path). */
static igraph_error_t igraph_i_community_leiden_run_overlapping(
        const igraph_t *graph,
        const igraph_vector_t *edge_weights, const igraph_vector_t *node_weights,
        const igraph_real_t resolution_parameter, const igraph_real_t beta,
        const igraph_integer_t max_memberships, const igraph_bool_t start,
        const igraph_integer_t n_iterations,
        const igraph_bool_t allow_isolation, const igraph_bool_t only_local_moving,
        igraph_vector_int_list_t *memberships, igraph_integer_t *nb_clusters,
        igraph_real_t *quality) {
    const igraph_integer_t n = igraph_vcount(graph);
    igraph_vector_t *i_edge_weights, *i_node_weights;
    igraph_integer_t i_nb_clusters;
    igraph_bool_t changed = true;
    igraph_real_t q_prev = -IGRAPH_INFINITY, q_cur;

    if (!nb_clusters) {
        nb_clusters = &i_nb_clusters;
    }

    if (!memberships) {
        IGRAPH_ERROR("Membership list must be provided for overlapping Leiden.",
                     IGRAPH_EINVAL);
    }
    if (igraph_is_directed(graph)) {
        IGRAPH_ERROR("Leiden algorithm is only implemented for undirected graphs.",
                     IGRAPH_EINVAL);
    }
    if (edge_weights && igraph_vector_size(edge_weights) != igraph_ecount(graph)) {
        IGRAPH_ERROR("Edge weight vector length does not match the number of edges.",
                     IGRAPH_EINVAL);
    }
    if (node_weights && igraph_vector_size(node_weights) != n) {
        IGRAPH_ERROR("Node weight vector length does not match the number of vertices.",
                     IGRAPH_EINVAL);
    }

    if (start && igraph_vector_int_list_size(memberships) != n) {
        IGRAPH_ERROR("Initial membership list length does not equal the number of vertices.",
                     IGRAPH_EINVAL);
    }

    if (!edge_weights) {
        i_edge_weights = IGRAPH_CALLOC(1, igraph_vector_t);
        IGRAPH_CHECK_OOM(i_edge_weights, "Overlapping Leiden algorithm failed, could not allocate memory for edge weights.");
        IGRAPH_FINALLY(igraph_free, i_edge_weights);
        IGRAPH_CHECK(igraph_vector_init(i_edge_weights, igraph_ecount(graph)));
        IGRAPH_FINALLY(igraph_vector_destroy, i_edge_weights);
        igraph_vector_fill(i_edge_weights, 1);
    } else {
        i_edge_weights = (igraph_vector_t *) edge_weights;
    }

    if (!node_weights) {
        i_node_weights = IGRAPH_CALLOC(1, igraph_vector_t);
        IGRAPH_CHECK_OOM(i_node_weights, "Overlapping Leiden algorithm failed, could not allocate memory for node weights.");
        IGRAPH_FINALLY(igraph_free, i_node_weights);
        IGRAPH_CHECK(igraph_vector_init(i_node_weights, n));
        IGRAPH_FINALLY(igraph_vector_destroy, i_node_weights);
        igraph_vector_fill(i_node_weights, 1);
    } else {
        i_node_weights = (igraph_vector_t *) node_weights;
    }

    if (start) {
        /* Start from the provided cover: validate it, clean it up (sort +
         * dedup each membership vector) and compact its community IDs. */
        IGRAPH_CHECK(igraph_i_community_leiden_ov_validate_start(n, max_memberships, memberships));
        IGRAPH_CHECK(igraph_i_community_leiden_ov_compact(memberships, nb_clusters));
    } else {
        /* Start from the singleton cover: node v belongs to community v only. */
        IGRAPH_CHECK(igraph_vector_int_list_resize(memberships, n));
        for (igraph_integer_t v = 0; v < n; v++) {
            igraph_vector_int_t *sigma = igraph_vector_int_list_get_ptr(memberships, v);
            IGRAPH_CHECK(igraph_vector_int_resize(sigma, 1));
            VECTOR(*sigma)[0] = v;
        }
    }

    /* Iterate the three-phase cycle. Phase 1 strictly increases the exact
     * potential Phi = Q; the duplicate-collapse in the projection step is
     * the one operation outside the potential-game core, so for
     * n_iterations < 0 (when running the full cycle) we additionally
     * require strict quality improvement, which makes termination
     * unconditional. When only_local_moving is set, phase 1 alone is
     * monotonic in Phi, so looping until it stops changing anything is
     * sufficient on its own, exactly as in \ref igraph_community_leiden(). */
    for (igraph_integer_t itr = 0;
         only_local_moving || n_iterations < 0 ? changed : itr < n_iterations;
         itr++) {
        changed = false;
        IGRAPH_CHECK(igraph_i_community_leiden_ov_iteration(graph, i_edge_weights,
                     i_node_weights, resolution_parameter, beta, max_memberships,
                     &allow_isolation, only_local_moving, memberships, &changed));
        if (!only_local_moving && n_iterations < 0 && changed) {
            IGRAPH_CHECK(igraph_i_community_leiden_ov_quality(graph, i_edge_weights,
                         i_node_weights, memberships, resolution_parameter, &q_cur));
            if (q_cur <= q_prev) {
                break;
            }
            q_prev = q_cur;
        }
    }

    IGRAPH_CHECK(igraph_i_community_leiden_ov_compact(memberships, nb_clusters));

    if (quality) {
        IGRAPH_CHECK(igraph_i_community_leiden_ov_quality(graph, i_edge_weights,
                     i_node_weights, memberships, resolution_parameter, quality));
    }

    if (!edge_weights) {
        igraph_vector_destroy(i_edge_weights);
        IGRAPH_FREE(i_edge_weights);
        IGRAPH_FINALLY_CLEAN(2);
    }

    if (!node_weights) {
        igraph_vector_destroy(i_node_weights);
        IGRAPH_FREE(i_node_weights);
        IGRAPH_FINALLY_CLEAN(2);
    }

    return IGRAPH_SUCCESS;
}


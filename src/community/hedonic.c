/* -*- mode: C -*-  */
/* vim:set ts=4 sw=4 sts=4 et: */
/*
   IGraph library.
   Copyright (C) 2007-2012  Gabor Csardi <csardi.gabor@gmail.com>
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
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301 USA

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
#include "igraph_vector.h"
#include "igraph_vector_list.h"

#include "core/interruption.h"

/* Move nodes in order to improve the quality of a partition.
 *
 * This function considers each node and greedily moves it to a neighboring
 * community that maximizes the improvement in the quality of a partition.
 * Only moves that strictly improve the quality are considered.
 *
 * The nodes are examined in a queue, and initially all nodes are put in the
 * queue in a random order. Nodes are popped from the queue when they are
 * examined, and only neighbors of nodes that are moved (which are not part of
 * the cluster the node was moved to) are pushed to the queue again.
 *
 * The \c membership vector is used as the starting point to move around nodes,
 * and is updated in-place.
 *
 */
static igraph_error_t igraph_i_community_hedonic_fastmovenodes(
        const igraph_t *graph,
        const igraph_inclist_t *edges_per_node,
        const igraph_vector_t *edge_weights, const igraph_vector_t *node_weights,
        const igraph_real_t resolution_parameter,
        igraph_integer_t *nb_clusters,
        igraph_vector_int_t *membership,
        igraph_bool_t *changed) {

    igraph_dqueue_int_t unstable_nodes;
    igraph_real_t max_diff = 0.0, diff = 0.0;
    const igraph_integer_t n = igraph_vcount(graph);
    igraph_bitset_t neighbor_cluster_added, node_is_stable;
    igraph_vector_t cluster_weights, edge_weights_per_cluster;
    igraph_vector_int_t neighbor_clusters;
    igraph_vector_int_t node_order;
    igraph_vector_int_t nb_nodes_per_cluster;
    igraph_stack_int_t empty_clusters;
    igraph_integer_t c, nb_neigh_clusters;
    int iter = 0;

    /* Initialize queue of unstable nodes and whether node is stable. Only
     * unstable nodes are in the queue. */
    IGRAPH_BITSET_INIT_FINALLY(&node_is_stable, n);

    IGRAPH_DQUEUE_INT_INIT_FINALLY(&unstable_nodes, n);

    /* Shuffle nodes */
    IGRAPH_CHECK(igraph_vector_int_init_range(&node_order, 0, n));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &node_order);
    IGRAPH_CHECK(igraph_vector_int_shuffle(&node_order));

    /* Add to the queue */
    for (igraph_integer_t i = 0; i < n; i++) {
        IGRAPH_CHECK(igraph_dqueue_int_push(&unstable_nodes, VECTOR(node_order)[i]));
    }

    /* Initialize cluster weights and nb nodes */
    IGRAPH_VECTOR_INIT_FINALLY(&cluster_weights, n);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&nb_nodes_per_cluster, n);
    for (igraph_integer_t i = 0; i < n; i++) {
        c = VECTOR(*membership)[i];
        VECTOR(cluster_weights)[c] += VECTOR(*node_weights)[i];
        VECTOR(nb_nodes_per_cluster)[c] += 1;
    }

    /* Initialize empty clusters */
    IGRAPH_STACK_INT_INIT_FINALLY(&empty_clusters, n);
    for (c = 0; c < n; c++)
        if (VECTOR(nb_nodes_per_cluster)[c] == 0) {
            IGRAPH_CHECK(igraph_stack_int_push(&empty_clusters, c));
        }

    /* Initialize vectors to be used in calculating differences */
    IGRAPH_VECTOR_INIT_FINALLY(&edge_weights_per_cluster, n);

    /* Initialize neighboring cluster */
    IGRAPH_BITSET_INIT_FINALLY(&neighbor_cluster_added, n);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&neighbor_clusters, n);

    /* Iterate while the queue is not empty */
    while (!igraph_dqueue_int_empty(&unstable_nodes)) {
        igraph_integer_t v = igraph_dqueue_int_pop(&unstable_nodes);
        igraph_integer_t best_cluster, current_cluster = VECTOR(*membership)[v];
        igraph_integer_t degree;
        igraph_vector_int_t *edges;

        /* Remove node from current cluster */
        VECTOR(cluster_weights)[current_cluster] -= VECTOR(*node_weights)[v];
        VECTOR(nb_nodes_per_cluster)[current_cluster]--;
        if (VECTOR(nb_nodes_per_cluster)[current_cluster] == 0) {
            IGRAPH_CHECK(igraph_stack_int_push(&empty_clusters, current_cluster));
        }

        /* Find out neighboring clusters */
        c = igraph_stack_int_top(&empty_clusters);
        VECTOR(neighbor_clusters)[0] = c;
        IGRAPH_BIT_SET(neighbor_cluster_added, c);
        nb_neigh_clusters = 1;

        /* Determine the edge weight to each neighboring cluster */
        edges = igraph_inclist_get(edges_per_node, v);
        degree = igraph_vector_int_size(edges);
        for (igraph_integer_t i = 0; i < degree; i++) {
            igraph_integer_t e = VECTOR(*edges)[i];
            igraph_integer_t u = IGRAPH_OTHER(graph, e, v);
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
        max_diff = VECTOR(edge_weights_per_cluster)[current_cluster] - VECTOR(*node_weights)[v] * VECTOR(cluster_weights)[current_cluster] * resolution_parameter;
        for (igraph_integer_t i = 0; i < nb_neigh_clusters; i++) {
            c = VECTOR(neighbor_clusters)[i];
            diff = VECTOR(edge_weights_per_cluster)[c] - VECTOR(*node_weights)[v] * VECTOR(cluster_weights)[c] * resolution_parameter;
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

        /* Move node to best cluster */
        VECTOR(cluster_weights)[best_cluster] += VECTOR(*node_weights)[v];
        VECTOR(nb_nodes_per_cluster)[best_cluster]++;
        if (best_cluster == igraph_stack_int_top(&empty_clusters)) {
            igraph_stack_int_pop(&empty_clusters);
        }

        /* Mark node as stable */
        IGRAPH_BIT_SET(node_is_stable, v);

        /* Add stable neighbours that are not part of the new cluster to the queue */
        if (best_cluster != current_cluster) {
            *changed = true;
            VECTOR(*membership)[v] = best_cluster;

            for (igraph_integer_t i = 0; i < degree; i++) {
                igraph_integer_t e = VECTOR(*edges)[i];
                igraph_integer_t u = IGRAPH_OTHER(graph, e, v);
                if (IGRAPH_BIT_TEST(node_is_stable, u) && VECTOR(*membership)[u] != best_cluster) {
                    IGRAPH_CHECK(igraph_dqueue_int_push(&unstable_nodes, u));
                    IGRAPH_BIT_CLEAR(node_is_stable, u);
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
    igraph_vector_int_destroy(&nb_nodes_per_cluster);
    igraph_vector_destroy(&cluster_weights);
    igraph_vector_int_destroy(&node_order);
    igraph_dqueue_int_destroy(&unstable_nodes);
    igraph_bitset_destroy(&node_is_stable);
    IGRAPH_FINALLY_CLEAN(9);

    return IGRAPH_SUCCESS;
}

/* Calculate the quality of the partition.
 *
 * The quality is defined as
 *
 * 1 / 2m sum_ij (A_ij - gamma n_i n_j)d(s_i, s_j)
 *
 * where m is the total edge weight, A_ij is the weight of edge (i, j), gamma is
 * the so-called resolution parameter, n_i is the node weight of node i, s_i is
 * the cluster of node i and d(x, y) = 1 if and only if x = y and 0 otherwise.
 *
 * Note that by setting n_i = k_i the degree of node i and dividing gamma by 2m,
 * we effectively optimize modularity. By setting n_i = 1 we optimize the
 * Constant Potts Model.
 *
 * This can be represented as a sum over clusters as
 *
 * 1 / 2m sum_c (e_c - gamma N_c^2)
 *
 * where e_c = sum_ij A_ij d(s_i, c)d(s_j, c) is (twice) the internal edge
 * weight in cluster c and N_c = sum_i n_i d(s_i, c) is the sum of the node
 * weights inside cluster c. This is how the quality is calculated in practice.
 *
 */
static igraph_error_t igraph_i_community_hedonic_quality(
        const igraph_t *graph, const igraph_vector_t *edge_weights, const igraph_vector_t *node_weights,
        const igraph_vector_int_t *membership, const igraph_integer_t nb_comms, const igraph_real_t resolution_parameter,
        igraph_real_t *quality) {
    igraph_vector_t cluster_weights;
    igraph_real_t total_edge_weight = 0.0;
    igraph_eit_t eit;
    igraph_integer_t i, c, n = igraph_vcount(graph);

    *quality = 0.0;

    /* Create the edgelist */
    IGRAPH_CHECK(igraph_eit_create(graph, igraph_ess_all(IGRAPH_EDGEORDER_ID), &eit));
    IGRAPH_FINALLY(igraph_eit_destroy, &eit);

    while (!IGRAPH_EIT_END(eit)) {
        igraph_integer_t e = IGRAPH_EIT_GET(eit);
        igraph_integer_t from = IGRAPH_FROM(graph, e), to = IGRAPH_TO(graph, e);
        total_edge_weight += VECTOR(*edge_weights)[e];
        /* We add the internal edge weights */
        if (VECTOR(*membership)[from] == VECTOR(*membership)[to]) {
            *quality += 2 * VECTOR(*edge_weights)[e];
        }
        IGRAPH_EIT_NEXT(eit);
    }
    igraph_eit_destroy(&eit);
    IGRAPH_FINALLY_CLEAN(1);

    /* Initialize cluster weights and nb nodes */
    IGRAPH_VECTOR_INIT_FINALLY(&cluster_weights, n);
    for (i = 0; i < n; i++) {
        c = VECTOR(*membership)[i];
        VECTOR(cluster_weights)[c] += VECTOR(*node_weights)[i];
    }

    /* We subtract gamma * N_c^2 */
    for (c = 0; c < nb_comms; c++) {
        *quality -= resolution_parameter * VECTOR(cluster_weights)[c] * VECTOR(cluster_weights)[c];
    }

    igraph_vector_destroy(&cluster_weights);
    IGRAPH_FINALLY_CLEAN(1);

    /* We normalise by 2m */
    *quality /= (2.0 * total_edge_weight);

    return IGRAPH_SUCCESS;
}

/* This is the core of the Hedonic Games algorithm and relies on subroutines to
 * perform the three different phases: (1) local moving of nodes, (2)
 * refinement of the partition and (3) aggregation of the network based on the
 * refined partition, using the non-refined partition to create an initial
 * partition for the aggregate network.
 */
static igraph_error_t igraph_i_community_hedonic(
        const igraph_t *graph,
        igraph_vector_t *edge_weights, igraph_vector_t *node_weights,
        const igraph_real_t resolution_parameter, const igraph_real_t beta,
        igraph_vector_int_t *membership, igraph_integer_t *nb_clusters, igraph_real_t *quality,
        igraph_bool_t *changed) {
    igraph_integer_t nb_refined_clusters;
    igraph_integer_t i, c, n = igraph_vcount(graph);
    igraph_t aggregated_graph, *i_graph;
    igraph_vector_t aggregated_edge_weights, aggregated_node_weights;
    igraph_vector_int_t aggregated_membership;
    igraph_vector_t *i_edge_weights, *i_node_weights;
    igraph_vector_int_t *i_membership;
    igraph_vector_t tmp_edge_weights, tmp_node_weights;
    igraph_vector_int_t tmp_membership;
    igraph_vector_int_t refined_membership;
    igraph_vector_int_t aggregate_node;
    igraph_vector_int_list_t clusters;
    igraph_inclist_t edges_per_node;
    igraph_bool_t continue_clustering;
    igraph_integer_t level = 0;

    /* Initialize temporary weights and membership to be used in aggregation */
    IGRAPH_VECTOR_INIT_FINALLY(&tmp_edge_weights, 0);
    IGRAPH_VECTOR_INIT_FINALLY(&tmp_node_weights, 0);
    IGRAPH_VECTOR_INT_INIT_FINALLY(&tmp_membership, 0);

    /* Initialize clusters */
    IGRAPH_VECTOR_INT_LIST_INIT_FINALLY(&clusters, n);

    /* Initialize aggregate nodes, which initially is identical to simply the
     * nodes in the graph. */
    IGRAPH_CHECK(igraph_vector_int_init_range(&aggregate_node, 0, n));
    IGRAPH_FINALLY(igraph_vector_int_destroy, &aggregate_node);

    /* Initialize refined membership */
    IGRAPH_VECTOR_INT_INIT_FINALLY(&refined_membership, 0);

    /* Initialize aggregated graph */
    IGRAPH_CHECK(igraph_empty(&aggregated_graph, 0, IGRAPH_UNDIRECTED));
    IGRAPH_FINALLY(igraph_destroy, &aggregated_graph);

    /* Initialize aggregated edge weights */
    IGRAPH_VECTOR_INIT_FINALLY(&aggregated_edge_weights, 0);

    /* Initialize aggregated node weights */
    IGRAPH_VECTOR_INIT_FINALLY(&aggregated_node_weights, 0);

    /* Initialize aggregated membership */
    IGRAPH_VECTOR_INT_INIT_FINALLY(&aggregated_membership, 0);

    /* Set actual graph, weights and membership to be used. */
    i_graph = (igraph_t*)graph;
    i_edge_weights = edge_weights;
    i_node_weights = node_weights;
    i_membership = membership;

    /* Clean membership and count number of *clusters */

    IGRAPH_CHECK(igraph_reindex_membership(i_membership, NULL, nb_clusters));

    if (*nb_clusters > n) {
        IGRAPH_ERROR("Too many communities in membership vector.", IGRAPH_EINVAL);
    }

    /* We start out with no changes, whenever a node is moved, this will be set to true. */
    *changed = false;
    do {

        /* Get incidence list for fast iteration */
        IGRAPH_CHECK(igraph_inclist_init( i_graph, &edges_per_node, IGRAPH_ALL, IGRAPH_LOOPS_TWICE));
        IGRAPH_FINALLY(igraph_inclist_destroy, &edges_per_node);

        /* Move around the nodes in order to increase the quality */
        IGRAPH_CHECK(igraph_i_community_hedonic_fastmovenodes(i_graph,
                     &edges_per_node,
                     i_edge_weights, i_node_weights,
                     resolution_parameter,
                     nb_clusters,
                     i_membership,
                     changed));

        /* We only continue clustering if not all clusters are represented by a
         * single node yet
         */
        continue_clustering = (*nb_clusters < igraph_vcount(i_graph));

        if (continue_clustering) {
            /* Set original membership */
            if (level > 0) {
                for (i = 0; i < n; i++) {
                    igraph_integer_t v_aggregate = VECTOR(aggregate_node)[i];
                    VECTOR(*membership)[i] = VECTOR(*i_membership)[v_aggregate];
                }
            }

            /* Get node sets for each cluster. */
            IGRAPH_CHECK(igraph_i_community_get_clusters(i_membership, &clusters));

            /* Ensure refined membership is correct size */
            IGRAPH_CHECK(igraph_vector_int_resize(&refined_membership, igraph_vcount(i_graph)));

            /* Refine each cluster */
            nb_refined_clusters = 0;
            for (c = 0; c < *nb_clusters; c++) {
                igraph_vector_int_t* cluster = igraph_vector_int_list_get_ptr(&clusters, c);
                IGRAPH_CHECK(igraph_i_community_hedonic_mergenodes(i_graph,
                             &edges_per_node,
                             i_edge_weights, i_node_weights,
                             cluster, i_membership, c,
                             resolution_parameter, beta,
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

            /* Keep track of aggregate node. */
            for (i = 0; i < n; i++) {
                /* Current aggregate node */
                igraph_integer_t v_aggregate = VECTOR(aggregate_node)[i];
                /* New aggregate node */
                VECTOR(aggregate_node)[i] = VECTOR(refined_membership)[v_aggregate];
            }

            IGRAPH_CHECK(igraph_i_community_hedonic_aggregate(
                             i_graph, &edges_per_node, i_edge_weights, i_node_weights,
                             i_membership, &refined_membership, nb_refined_clusters,
                             &aggregated_graph, &tmp_edge_weights, &tmp_node_weights, &tmp_membership));

            /* On the lowest level, the actual graph and node and edge weights and
             * membership are used. On higher levels, we will use the aggregated graph
             * and associated vectors.
             */
            if (level == 0) {
                /* Set actual graph, weights and membership to be used. */
                i_graph = &aggregated_graph;
                i_edge_weights = &aggregated_edge_weights;
                i_node_weights = &aggregated_node_weights;
                i_membership = &aggregated_membership;
            }

            /* Update the aggregated administration. */
            IGRAPH_CHECK(igraph_vector_update(i_edge_weights, &tmp_edge_weights));
            IGRAPH_CHECK(igraph_vector_update(i_node_weights, &tmp_node_weights));
            IGRAPH_CHECK(igraph_vector_int_update(i_membership, &tmp_membership));

            level += 1;
        }

        /* We are done iterating, so we destroy the incidence list */
        igraph_inclist_destroy(&edges_per_node);
        IGRAPH_FINALLY_CLEAN(1);
    } while (continue_clustering);

    /* Free aggregated graph and associated vectors */
    igraph_vector_int_destroy(&aggregated_membership);
    igraph_vector_destroy(&aggregated_node_weights);
    igraph_vector_destroy(&aggregated_edge_weights);
    igraph_destroy(&aggregated_graph);
    IGRAPH_FINALLY_CLEAN(4);

    /* Free remaining memory */
    igraph_vector_int_destroy(&refined_membership);
    igraph_vector_int_destroy(&aggregate_node);
    igraph_vector_int_list_destroy(&clusters);
    igraph_vector_int_destroy(&tmp_membership);
    igraph_vector_destroy(&tmp_node_weights);
    igraph_vector_destroy(&tmp_edge_weights);
    IGRAPH_FINALLY_CLEAN(6);

    /* Calculate quality */
    if (quality) {
        IGRAPH_CHECK(igraph_i_community_hedonic_quality(graph, edge_weights, node_weights, membership, *nb_clusters, resolution_parameter, quality));
    }

    return IGRAPH_SUCCESS;
}

/**
 * \ingroup communities
 * \function igraph_community_hedonic
 * \brief Finding community structure using the Hedonic Games algorithm.
 *
 * This function implements the Hedonic Games algorithm for finding community
 * structure.
 *
 * </para><para>
 * It is similar to the multilevel algorithm, often called the Louvain
 * algorithm, but it is faster and yields higher quality solutions. It can
 * optimize both modularity and the Constant Potts Model, which does not suffer
 * from the resolution-limit (see Tragg, Van Dooren &amp; Nesterov).
 *
 * </para><para>
 * The Hedonic Games algorithm consists of three phases: (1) local moving of nodes, (2)
 * refinement of the partition and (3) aggregation of the network based on the
 * refined partition, using the non-refined partition to create an initial
 * partition for the aggregate network. In the local move procedure in the
 * Hedonic Games algorithm, only nodes whose neighborhood has changed are visited. Only
 * moves that strictly improve the quality function are made. The refinement is
 * done by restarting from a singleton partition within each cluster and
 * gradually merging the subclusters. When aggregating, a single cluster may
 * then be represented by several nodes (which are the subclusters identified in
 * the refinement).
 *
 * </para><para>
 * The Hedonic Games algorithm provides several guarantees. The Hedonic Games algorithm is
 * typically iterated: the output of one iteration is used as the input for the
 * next iteration. At each iteration all clusters are guaranteed to be
 * connected and well-separated. After an iteration in which nothing has
 * changed, all nodes and some parts are guaranteed to be locally optimally
 * assigned. Note that even if a single iteration did not result in any change,
 * it is still possible that a subsequent iteration might find some
 * improvement. Each iteration explores different subsets of nodes to consider
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
 * where m is the total edge weight, <code>A_ij</code> is the weight of edge
 * (i, j), \c γ is the so-called resolution parameter, <code>n_i</code>
 * is the node weight of node \c i, <code>s_i</code> is the cluster of node
 * \c i and <code>δ(x, y) = 1</code> if and only if <code>x = y</code> and 0
 * otherwise. By setting <code>n_i = k_i</code>, the degree of node \c i, and
 * dividing \c γ by <code>2m</code>, we effectively obtain an expression for
 * modularity. Hence, the standard modularity will be optimized when you supply
 * the degrees as \c node_weights and by supplying as a resolution parameter
 * <code>1/(2m)</code>, with \c m the number of edges.
 *
 * </para><para>
 * References:
 *
 * </para><para>
 * V. A. Traag, L. Waltman, N. J. van Eck:
 * From Louvain to Hedonic Games: guaranteeing well-connected communities.
 * Scientific Reports, 9(1), 5233 (2019).
 * http://dx.doi.org/10.1038/s41598-019-41695-z
 *
 * </para><para>
 * V. A. Traag, P. Van Dooren, and Y. Nesterov:
 * Narrow scope for resolution-limit-free community detection.
 * Phys. Rev. E 84, 016114 (2011).
 * https://doi.org/10.1103/PhysRevE.84.016114
 *
 * \param graph The input graph. It must be an undirected graph.
 * \param edge_weights Numeric vector containing edge weights. If \c NULL, every edge
 *    has equal weight of 1. The weights need not be non-negative.
 * \param node_weights Numeric vector containing node weights. If \c NULL, every node
 *    has equal weight of 1.
 * \param resolution_parameter The resolution parameter used, which is
 *    represented by gamma in the objective function mentioned in the
 *    documentation.
 * \param beta The randomness used in the refinement step when merging. A small
 *    amount of randomness (\c beta = 0.01) typically works well.
 * \param start Start from membership vector. If this is true, the optimization
 *    will start from the provided membership vector. If this is false, the
 *    optimization will start from a singleton partition.
 * \param n_iterations Iterate the core Hedonic Games algorithm for the indicated number
 *    of times. If this is a negative number, it will continue iterating until
 *    an iteration did not change the clustering.
 * \param membership The membership vector. This is both used as the initial
 *    membership from which optimisation starts and is updated in place. It
 *    must hence be properly initialized. When finding clusters from scratch it
 *    is typically started using a singleton clustering. This can be achieved
 *    using \ref igraph_vector_int_init_range().
 * \param nb_clusters The number of clusters contained in \c membership.
 *    If \c NULL, the number of clusters will not be returned.
 * \param quality The quality of the partition, in terms of the objective
 *    function as included in the documentation. If \c NULL the quality will
 *    not be calculated.
 * \return Error code.
 *
 * Time complexity: near linear on sparse graphs.
 *
 * \example examples/simple/igraph_community_hedonic.c
 */
igraph_error_t igraph_community_hedonic(const igraph_t *graph,
                            const igraph_vector_t *edge_weights, const igraph_vector_t *node_weights,
                            const igraph_real_t resolution_parameter, const igraph_real_t beta, const igraph_bool_t start,
                            const igraph_integer_t n_iterations,
                            igraph_vector_int_t *membership, igraph_integer_t *nb_clusters, igraph_real_t *quality) {
    igraph_vector_t *i_edge_weights, *i_node_weights;
    igraph_integer_t i_nb_clusters;
    igraph_integer_t n = igraph_vcount(graph);

    if (!nb_clusters) {
        nb_clusters = &i_nb_clusters;
    }

    if (start) {
        if (!membership) {
            IGRAPH_ERROR("Cannot start optimization if membership is missing.", IGRAPH_EINVAL);
        }

        if (igraph_vector_int_size(membership) != n) {
            IGRAPH_ERROR("Initial membership length does not equal the number of vertices.", IGRAPH_EINVAL);
        }
    } else {
        if (!membership)
            IGRAPH_ERROR("Membership vector should be supplied and initialized, "
                         "even when not starting optimization from it.", IGRAPH_EINVAL);

        IGRAPH_CHECK(igraph_vector_int_range(membership, 0, n));
    }


    if (igraph_is_directed(graph)) {
        IGRAPH_ERROR("Hedonic Games algorithm is only implemented for undirected graphs.", IGRAPH_EINVAL);
    }

    /* Check edge weights to possibly use default */
    if (!edge_weights) {
        i_edge_weights = IGRAPH_CALLOC(1, igraph_vector_t);
        IGRAPH_CHECK_OOM(i_edge_weights, "Hedonic Games algorithm failed, could not allocate memory for edge weights.");
        IGRAPH_FINALLY(igraph_free, i_edge_weights);
        IGRAPH_CHECK(igraph_vector_init(i_edge_weights, igraph_ecount(graph)));
        IGRAPH_FINALLY(igraph_vector_destroy, i_edge_weights);
        igraph_vector_fill(i_edge_weights, 1);
    } else {
        i_edge_weights = (igraph_vector_t*)edge_weights;
    }

    /* Check edge weights to possibly use default */
    if (!node_weights) {
        i_node_weights = IGRAPH_CALLOC(1, igraph_vector_t);
        IGRAPH_CHECK_OOM(i_node_weights, "Hedonic Games algorithm failed, could not allocate memory for node weights.");
        IGRAPH_FINALLY(igraph_free, i_node_weights);
        IGRAPH_CHECK(igraph_vector_init(i_node_weights, n));
        IGRAPH_FINALLY(igraph_vector_destroy, i_node_weights);
        igraph_vector_fill(i_node_weights, 1);
    } else {
        i_node_weights = (igraph_vector_t*)node_weights;
    }

    /* Perform actual Hedonic Games algorithm iteratively. We either
     * perform a fixed number of iterations, or we perform
     * iterations until the quality remains unchanged. Even if
     * a single iteration did not change anything, a subsequent
     * iteration may still find some improvement. This is because
     * each iteration explores different subsets of nodes.
     */
    igraph_bool_t changed = false;
    for (igraph_integer_t itr = 0;
         n_iterations >= 0 ? itr < n_iterations : !changed;
         itr++) {
        IGRAPH_CHECK(igraph_i_community_hedonic(graph, i_edge_weights, i_node_weights,
                                               resolution_parameter, beta,
                                               membership, nb_clusters, quality, &changed));
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

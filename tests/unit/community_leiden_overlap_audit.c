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

int main(void) {
    const igraph_real_t resolutions[] = { -0.4, -0.05, 0.0, 0.02, 0.1, 0.35, 1.0 };
    const igraph_int_t n_resolutions = sizeof(resolutions) / sizeof(resolutions[0]);
    igraph_int_t audited = 0, runs = 0;
    igraph_real_t worst = 0.0;

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

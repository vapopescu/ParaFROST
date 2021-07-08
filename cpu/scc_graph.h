/***********************************************************************[pfsimp.h]
Copyright(c) 2020, Muhammad Osama - Anton Wijs,
Technische Universiteit Eindhoven (TU/e).

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
**********************************************************************************/

#pragma once

#include "pfsolve.h"
#include "gm.h"

#include <omp.h>

namespace pFROST {
	class scc_graph : public gm_graph {
    protected:
        const IG* _ig;

        inline node_t add_node() {
            if (_frozen) thaw();

            node_t n = _numNodes++;

            std::vector<edge_dest_t> T;  // empty vector
            flexible_graph[n] = T; // T is copied

            return n + 1;
        }

        inline edge_t add_edge(node_t n, node_t m) {
            assert(is_node(n));
            assert(is_node(m));

            if (_frozen) thaw();

            edge_t e = _numEdges++;

            edge_dest_t T;
            T.dest = m;
            T.edge = e;

            flexible_graph[n].push_back(T);

            return e + 1;
        }

	public:
        inline void set_graph(const IG& ig) { _ig = &ig; }

        inline void update_graph() {
            clear_graph();

            for (uint32 i = 0; i < inf.nDualVars; i++) {
                add_node();
            }

            pfrost->workerPool.doWorkForEach((uint32)0, inf.nDualVars, [&](uint32 i) {
                for (uint32 j = 0; j < (*_ig)[i].children().size(); j++) {
                    if (!(*_ig)[i].children()[j].second->deleted()) {
                        add_edge(i, (*_ig)[i].children()[j].first);
                    }
                }
            });
            pfrost->workerPool.join();
        }

		inline void freeze() {
            if (_frozen) return;

            node_t n_nodes = num_nodes();
            edge_t n_edges = num_edges();

            allocate_memory_for_frozen_graph(n_nodes, n_edges);

            e_idx2id = new edge_t[n_edges];
            e_id2idx = new edge_t[n_edges];

            // iterate over graph and make new structure
            edge_t next_edge = 0;
            for (node_t i = 0; i < n_nodes; i++) {
                std::vector<edge_dest_t>& Nbrs = flexible_graph[i];
                begin[i] = next_edge;

                std::vector<edge_dest_t>::iterator I;
                for (I = Nbrs.begin(); I != Nbrs.end(); I++) {
                    node_id dest = (*I).dest;         // for node ID = IDX
                    edge_id edgeID = (*I).edge;

                    node_idx[next_edge] = dest;

                    e_idx2id[next_edge] = edgeID;      // IDX and ID are different for edge
                    e_id2idx[edgeID] = next_edge;

                    next_edge++;
                }
            }
            begin[n_nodes] = next_edge;

            _frozen = true;
            _semi_sorted = false;
            _reverse_edge = false;

            // compute helper data
            do_semi_sort();
            make_reverse_edges();
		}

		inline void thaw() {
            if (!_frozen) return;

            delete_frozen_graph();

            _frozen = false;
            _semi_sorted = false;
            _reverse_edge = false;
		}
	};
}
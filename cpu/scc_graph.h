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

#include <atomic>
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

		inline void freeze() {
            if (_frozen) return;

            std::atomic<int> threadIdx;
            std::atomic<uint32> numEdges = 0;
            uint32* out_degree = new uint32[inf.nDualVars];

            uint32 batchSize = inf.nDualVars / pfrost->workerPool.count();
            uint32 remainder = inf.nDualVars % pfrost->workerPool.count();

            pfrost->workerPool.doWork([&] {
                int tid = threadIdx++;
                uint32 n = 0;

                uint32 begin = batchSize * tid + std::min((uint32)tid, remainder);
                uint32 end = begin + batchSize + (tid < remainder ? 1 : 0);

                for (uint32 i = begin; i < end; i++) {
                    uint32 deg = 0;
                    for (uint32 j = 0; j < (*_ig)[i].children().size(); j++) {
                        if (!(*_ig)[i].children()[j].second->deleted()) deg++;
                    }
                    out_degree[i] = deg;
                    n += deg;
                }

                numEdges += n;
            });
            pfrost->workerPool.join();

            node_t n_nodes = (node_t)inf.nDualVars;
            edge_t n_edges = (edge_t)numEdges;

            allocate_memory_for_frozen_graph(n_nodes, n_edges);

            e_idx2id = new edge_t[n_edges];
            e_id2idx = new edge_t[n_edges];

            // calculate beginning for each edge
            begin[0] = 0;
            for (node_t i = 0; i < n_nodes; i++) {
                begin[i+1] = begin[i] + out_degree[i];
            }
            delete[] out_degree;
            assert(begin[n_nodes] == n_edges);

            // iterate over graph and make new structure
            pfrost->workerPool.doWorkForEach((node_t)0, n_nodes, [&](node_t i) {
                const uint32& lit1 = (uint32)i;
                edge_t next_edge = begin[i];

                for (uint32 j = 0; j < (*_ig)[lit1].children().size(); j++) {
                    if (!(*_ig)[lit1].children()[j].second->deleted()) {
                        const uint32& lit2 = (*_ig)[lit1].children()[j].first;

                        node_idx[next_edge] = (node_id)lit2;
                        e_idx2id[next_edge] = next_edge;
                        e_id2idx[next_edge] = next_edge;

                        next_edge++;
                    }
                }

                assert(next_edge == begin[i + 1]);
            });
            pfrost->workerPool.join();

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
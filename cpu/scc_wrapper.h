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
#include "scc.h"
#include "my_work_queue.h"
#include "common_main.h"
#include "gm.h"
#include "scc_graph.h"

#include <omp.h>

extern node_t* G_SCC;
extern int32_t G_num_nodes;

namespace pFROST {

	enum scc_method {
		SCC_TARJAN,
		SCC_UFSCC
	};

	class SCCWrapper : main_t {
	protected: 
		scc_graph G;
		unsigned int method;

		inline bool run() {
			switch (method) {
			case SCC_TARJAN:
				do_tarjan_all(G);
				return true;
			case SCC_UFSCC:
				do_ufscc_all(G);
				return true;
			default:
				break;
			}

			return false;
		}

	public:
		inline void setNumThreads(const unsigned int& num_threads) { this->num_threads = num_threads; }
		inline void setMethod(const unsigned int& method) { this->method = method; }
		inline void setGraph(const IG& ig) { G.set_graph(ig); }
		inline void updateGraph() { G.update_graph(); }

		inline node_t* getSCC() {
			// Initialize
			gm_rt_initialize();
			omp_set_num_threads(num_threads);
			G.freeze();

			G_num_nodes = G.num_nodes();
			G_SCC = new node_t[G.num_nodes()];

			#pragma omp parallel for
			for (int i = 0; i < G_num_nodes; i++)
				G_SCC[i] = gm_graph::NIL_NODE;

			work_q_init(gm_rt_get_num_threads());  // called at the beginning
			initialize_color();
			// initialize_analyze();

			switch (method) {
			case SCC_TARJAN: // Tarjan
				initialize_tarjan();
				break;
			case SCC_UFSCC: // UFSCC
				initialize_ufscc();
				break;
			}

			// Run
			run();

			// Cleanup
			finalize_color();
			//finalize_analyze();
			switch (method) {
			case SCC_TARJAN:
				break;
			case SCC_UFSCC:
				finalize_ufscc();
				break;
			default:
				break;
		}

			return G_SCC;
		}
	};
}
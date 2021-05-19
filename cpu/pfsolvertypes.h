/***********************************************************************[pfsolvertypes.h]
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

#ifndef __SOLVER_TYPES_
#define __SOLVER_TYPES_

#include "pfspace.h"
#include "pfwatch.h"
#include "pfsclause.h"
#include "pfnode.h"
#include "pfvec.h"
#include <atomic>

namespace pFROST {
	/*****************************************************/
	/*  Global vector types for CNF/occur lists          */
	/*****************************************************/
	typedef Vec<C_REF> BCNF;
	typedef Vec<WATCH, int> WL;
	typedef Vec<WL> WT;
	typedef Vec<uint32, int> BOL;
	typedef Vec<C_REF, int> WOL;
	typedef Vec<S_REF, int> OL;
	typedef Vec<OL> OT;
	typedef Vec<Node> IG;
	typedef Vec<S_REF, size_t> SCNF;
	/*****************************************************/
	/*  Global structures and comparators		         */
	/*****************************************************/
	struct LEARN {
		int64 lastreduce;
		int64 bumped, subtried, elim_marked, elim_lastmarked;
		int64 subsume_conf_max, sigma_conf_max, mdm_conf_max, reduce_conf_max;
		int64 restarts_conf_max, stable_conf_max, map_conf_max;
		int64 rephased[2], rephase_conf_max, rephase_last_max;
		double var_inc, var_decay;
		uint32 numMDs, nRefVars;
		uint32 best, target;
		int keptsize, keptlbd;
		int	rounds;
		LIT_ST lastrephased;
		bool stable;

		LEARN() { memset(this, 0, sizeof(*this)); }
	};
	struct STATS {
		std::atomic<int64> sysMemAvail;
		std::atomic<int64> n_rephs, n_randrephs;
		std::atomic<int64> n_subchecks, n_subcalls;
		std::atomic<int64> n_allsubsumed, n_allstrengthened, n_learntsubs;
		std::atomic<int64> n_triedreduns, n_orgreduns, n_lrnreduns;
		std::atomic<int64> n_fuds, n_mds;
		std::atomic<int64> n_units, n_props, n_forced;
		std::atomic<int64> tot_lits, max_lits, n_glues;
		std::atomic<int64> reuses, reduces, recyclings;
		std::atomic<int64> stab_restarts, ncbt, cbt;
		std::atomic<int> sigmifications;
		std::atomic<int> marker, mdm_calls;
		std::atomic<int> mappings, shrinkages;

		STATS() { memset(this, 0, sizeof(*this)); }
	};
	struct CSIZE {
		C_REF ref;
		size_t size;
		CSIZE() {}
		CSIZE(const C_REF& _r, const int& _s) : ref(_r), size(_s) {}
	};
}

#endif
/***********************************************************************[pfoptions.h]
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

#ifndef __SOLVER_OPTS_
#define __SOLVER_OPTS_

#include <cstring>
#include "pfdtypes.h"
#include "pfargs.h"

namespace pFROST {

	struct OPTION {
		//==========================================//
		//             Solver options               //
		//==========================================//
		LIT_ST	polarity;
		//------------------------------------------//
		string	proof_path;
		//------------------------------------------//
		int64	stabrestart_inc;
		int64	learntsub_max;
		//------------------------------------------//
		uint32	sigma_min, sigma_inc;
		uint32	map_min, map_inc;
		//------------------------------------------//
		double	var_inc, var_decay;
		double	stabrestart_rate;
		double	lbd_rate;
		double	gc_perc;
		double	map_perc;
		double	reduce_perc;
		//------------------------------------------//
		int		timeout;
		int		seed;
		int		prograte;
		int		chrono_min;
		int		reduce_inc;
		int		restart_inc;
		int		rephase_inc;
		int		bumpreason_depth;
		int		lbd_tier2, lbd_tier1, lbd_fast, lbd_slow;
		int		luby_inc, luby_max;
		int		minimizebin_max, minimize_depth;
		int		mdm_rounds,	mdm_freq, mdm_div, mdm_minc, mdm_sinc, mdm_vsids_pumps, mdm_vmfq_pumps;
		int		subsume_inc, subsume_min_occs, subsume_min_checks, subsume_max_checks, subsume_max_csize;
		int		hbr_max, rse_max;
		int		worker_count;
		//------------------------------------------//
		bool	model_en;
		bool	proof_en;
		bool	report_en;
		bool	chrono_en;
		bool	stable_en;
		bool	reduce_en;
		bool	subsume_en;
		bool	parse_only_en;
		bool	priorbins_en;
		bool	reusetrail_en;
		bool	chronoreuse_en;
		bool	bumpreason_en;
		bool	target_phase_en, rephase_en;
		bool	vsids_en, mdmvsidsonly_en, vsidsonly_en;
		bool	mdmfusem_en, mdmfuses_en, mdm_mcv_en;
		//==========================================//
		//             Simplifier options           //
		//==========================================//
		bool	hse_en;
		bool	bce_en;
		bool	ere_en;
		bool	igr_en;
		bool	hbr_en;
		bool	hla_en;
		bool	ce_en;
		bool	all_en;
		bool	solve_en;
		bool	aggr_cnf_sort;
		bool	profile_simp;
		bool	ve_en, ve_plus_en;
		bool	sigma_en, sigma_live_en;
		//------------------------------------------//
		int		phases;
		int		shrink_rate;
		int		xor_max_arity;
		int		hse_limit, bce_limit, ere_limit;
		//------------------------------------------//
		uint32	lcve_min;
		uint32	lits_min;
		uint32	mu_pos, mu_neg;
		//------------------------------------------//
		OPTION() { memset(this, 0, sizeof(*this)); }
		void init();
	};

}

#endif


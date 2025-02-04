﻿/***********************************************************************[pfdefs.h]
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

#ifndef __GL_DEFS_
#define __GL_DEFS_
//=======================================//
//            C++ directives             //
//=======================================//
#include <iostream>
#include <algorithm>
#include <cstring>
#include <locale>
#include <cassert>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <climits>
#include <cstdlib>
#include <csignal>
#include <random>
#include <chrono>
#include <atomic>
#include "pflogging.h"
#include "pfdtypes.h"
#include "pfconst.h"

#ifdef __linux__ 
#include <sys/resource.h>
#include <sys/mman.h>
#include <sys/sysinfo.h>
#include <unistd.h>
#include <cpuid.h>
#elif _WIN32
#define NOMINMAX
#include <windows.h>
#include <psapi.h>
#include <intrin.h>
#include <Winnt.h>
#include <io.h>
#endif
#undef ERROR
using std::swap;
using std::string;
using std::ostream;
using std::fstream;
using std::ifstream;

#define IGR_COUNT 9

namespace pFROST {

	//===================================================//
	//       Global Data structures primitives           //
	//===================================================//
	struct OCCUR { std::atomic<uint32> ps, ns; };
	struct CNF_INFO {
		uint32 orgVars, maxVar, maxFrozen, maxMelted, nDualVars, n_del_vars_after;
		uint32 nOrgCls, nOrgLits, n_cls_after, n_lits_after;
		uint32 nClauses, nLiterals, nLearntLits;
		CNF_INFO() { memset(this, 0, sizeof(*this)); }
	};
	extern CNF_INFO inf;

	class TIMER {
	private:
		std::chrono::high_resolution_clock::time_point _start, _stop;
		std::chrono::high_resolution_clock::time_point _start_p, _stop_p;
		std::chrono::high_resolution_clock::time_point _timeout;
	public:
		float parse, solve, simp;
		float vo, ve, hse, bce, ere, cot, rot, sot, gc, io, ce, igr;
		float igr_part[IGR_COUNT];
		TIMER				() { memset(this, 0, sizeof(*this)); }
		void start			() { _start = std::chrono::high_resolution_clock::now(); }
		void stop			() { _stop = std::chrono::high_resolution_clock::now(); }
		float cpuTime		() { return ((float)std::chrono::duration_cast<std::chrono::milliseconds>(_stop - _start).count()) / 1000; }
		void pstart			() { _start_p = std::chrono::high_resolution_clock::now(); }
		void pstop			() { _stop_p = std::chrono::high_resolution_clock::now(); }
		float pcpuTime		() { return ((float)std::chrono::duration_cast<std::chrono::microseconds>(_stop_p - _start_p).count()) / 1000; }
		void setTimeout		(int seconds) { _timeout = std::chrono::high_resolution_clock::now() + std::chrono::seconds(seconds); }
		bool checkTimeout	() {
			std::chrono::high_resolution_clock::time_point now = std::chrono::high_resolution_clock::now();
			return std::chrono::duration_cast<std::chrono::milliseconds>(_timeout - now).count() < 0;
		}
	};
	//====================================================//
	//                 iterators & checkers               //
	//====================================================//
	template <class T>
	inline bool  _checkvar(const T VAR) {
		const bool invariant = VAR <= 0 || VAR > inf.maxVar;
		if (invariant)
			PFLOGEN("invariant \"VAR > 0 && VAR <= inf.maxVar\" failed on variable (%lld), bound = %lld",
				int64(VAR), int64(inf.maxVar));
		return !invariant;
	}
	template <class T>
	inline bool  _checklit(const T LIT) {
		const bool invariant = LIT <= 1 || LIT >= inf.nDualVars;
		if (invariant)
			PFLOGEN("invariant \"LIT > 1 && LIT < inf.nDualVars\" failed on literal (%lld), bound = %lld",
				int64(LIT), int64(inf.nDualVars));
		return !invariant;
	}
	#define CHECKVAR(VAR) assert(_checkvar(VAR))

	#define CHECKLIT(LIT) assert(_checklit(LIT))

	#define forall_variables(VAR) for (uint32 VAR = 1; VAR <= inf.maxVar; VAR++)

	#define forall_literals(LIT) for (uint32 LIT = 2; LIT < inf.nDualVars; LIT++)
	//====================================================//
	//                 Global Inline helpers              //
	//====================================================//
	template<class T>
	inline bool		eq				(T& in, arg_t ref) {
		while (*ref) { if (*ref != *in) return false; ref++; in++; }
		return true;
	}
	template<class T>
	inline bool		eqn				(T in, arg_t ref, const bool& lower = false) {
		if (lower) {
			while (*ref) {
				if (tolower(*ref) != tolower(*in))
					return false;
				ref++; in++;
			}
		}
		else {
			while (*ref) { if (*ref != *in) return false; ref++; in++; }
		}
		return true;
	}
	inline double	ratio			(const double& x, const double& y) { return y ? x / y : 0; }
	inline int		l2i				(const uint32& lit) { assert(lit > 1); return SIGN(lit) ? -int(ABS(lit)) : int(ABS(lit)); }
	inline uint32	maxInactive		() { return inf.maxMelted + inf.maxFrozen; }
	inline uint32	maxActive		() { assert(inf.maxVar >= maxInactive()); return inf.maxVar - maxInactive(); }
	inline uint32	maxLiterals		() { return inf.nLiterals + inf.nLearntLits; }
}

#endif // __GL_DEFS_


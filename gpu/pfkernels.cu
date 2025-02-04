/***********************************************************************[pfkernels.cu]
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

#include "pfdevice.cuh"
#include "pfbve.cuh"
#include "pfhse.cuh"
#include <cub/device/device_scan.cuh>

using namespace cub;

namespace pFROST {

	namespace SIGmA {

		template<class T>
		__global__ void memset_k(T* mem, T val, size_t size)
		{
			size_t tid = global_tx();
			while (tid < size) { mem[tid] = val; tid += stride_x(); }
		}

		__global__ void reset_stats(GSTATS* gstats) { gstats->numDelVars = 0, gstats->numClauses = 0, gstats->numLits = 0; }

		__global__ void prep_cnf_k(CNF* cnf)
		{
			uint32 tid = global_tx();
			while (tid < cnf->size()) { 
				SCLAUSE& c = cnf->clause(tid);
				devSort(c.data(), c.size());
				calcSig(c); 
				tid += stride_x();
			}
		}

		__global__ void reset_ot_k(OT* ot)
		{
			uint32 tid = global_tx();
			while (tid < ot->size()) { (*ot)[tid].clear(); tid += stride_x(); }
		}

		__global__ void reduce_ot(CNF* cnf, OT* ot)
		{
			uint32 tid = global_tx();
			while (tid < ot->size()) { reduceOL(*cnf, (*ot)[tid]); tid += stride_x(); }
		}

		__global__ void sort_ot_p(CNF* cnf, OT* ot, cuVecU* pVars)
		{
			uint32 tid = global_tx();
			while (tid < pVars->size()) {
				uint32 x = pVars->at(tid), p = V2L(x);
				assert(x);
				OL& ol = (*ot)[p];
				devSort(ol.data(), ol.size(), CNF_CMP_KEY(cnf));
				tid += stride_x();
			}
		}

		__global__ void sort_ot_n(CNF* cnf, OT* ot, cuVecU* pVars)
		{
			uint32 tid = global_tx();
			while (tid < pVars->size()) {
				uint32 x = pVars->at(tid), n = NEG(V2L(x));
				assert(x);
				OL& ol = (*ot)[n];
				devSort(ol.data(), ol.size(), CNF_CMP_KEY(cnf));
				tid += stride_x();
			}
		}

		__global__ void create_ot_k(CNF* cnf, OT* ot)
		{
			uint32 tid = global_tx();
			while (tid < cnf->size()) {
				S_REF r = cnf->ref(tid);
				SCLAUSE& c = (*cnf)[r];
				if (c.original() || c.learnt()) {
					uint32* lit = c, * cend = c.end();
#pragma unroll
					while (lit != cend) (*ot)[*lit++].insert(r);
				}
				tid += stride_x();
			}
		}

		__global__ void assign_scores(uint32* eligible, uint32* scores, uint32* hist, uint32 size)
		{
			uint32 tid = global_tx();
			while (tid < size) {
				uint32 v = tid + 1;
				uint32 p = V2L(v), ps = hist[p], ns = hist[NEG(p)];
				eligible[tid] = v;
				scores[v] = rscore(ps, ns);
				tid += stride_x();
			}
		}

		__global__ void assign_scores(uint32* eligible, uint32* scores, uint32* hist, OT* ot, uint32 size)
		{
			uint32 tid = global_tx();
			while (tid < size) {
				uint32 v = tid + 1;
				uint32 p = V2L(v), n = NEG(p), ps = (*ot)[p].size(), ns = (*ot)[n].size();
				hist[p] = ps, hist[n] = ns;
				eligible[tid] = v;
				scores[v] = rscore(ps, ns);
				tid += stride_x();
			}
		}

		__global__ void copy_if_k(uint32* dest, CNF* src, GSTATS* gstats)
		{
			uint32 tid = global_tx();
			while (tid < src->size()) {
				SCLAUSE& c = src->clause(tid);
				if (c.original() || c.learnt()) {
					uint32* d = dest + atomicAdd(&gstats->numLits, c.size());
					uint32* s = c, *cend = c.end();
#pragma unroll
					while (s != cend) *d++ = *s++;
				}
				tid += stride_x();
			}
		}

		__global__ void cnt_reds(CNF* cnf, GSTATS* gstats)
		{
			uint32* sh_rCls = SharedMemory<uint32>();
			uint32* sh_rLits = sh_rCls + blockDim.x;
			uint32 tid = global_tx_off();
			uint32 nCls = 0;
			uint32 nLits = 0;
			while (tid < cnf->size()) {
				SCLAUSE& c1 = cnf->clause(tid);
				if (c1.original() || c1.learnt())
					nCls++, nLits += c1.size();
				if (tid + blockDim.x < cnf->size()) {
					SCLAUSE& c2 = cnf->clause(tid + blockDim.x);
					if (c2.original() || c2.learnt())
						nCls++, nLits += c2.size();
				}
				tid += stride_x_off();
			}
			loadShared(sh_rCls, nCls, sh_rLits, nLits, cnf->size());
			sharedReduce(sh_rCls, nCls, sh_rLits, nLits);
			warpReduce(sh_rCls, nCls, sh_rLits, nLits);
			if (threadIdx.x == 0) {
				atomicAdd(&gstats->numClauses, nCls);
				atomicAdd(&gstats->numLits, nLits);
			}
		}

		__global__ void cnt_cls(CNF* cnf, GSTATS* gstats)
		{
			uint32* sh_rCls = SharedMemory<uint32>();
			uint32 tid = global_tx_off();
			uint32 nCls = 0;
			while (tid < cnf->size()) {
				SCLAUSE& c1 = cnf->clause(tid);
				if (c1.original() || c1.learnt()) nCls++;
				uint32 off = tid + blockDim.x;
				if (off < cnf->size()) {
					SCLAUSE& c2 = cnf->clause(off);
					if (c2.original() || c2.learnt()) nCls++;
				}
				tid += stride_x_off();
			}
			loadShared(sh_rCls, nCls, cnf->size());
			sharedReduce(sh_rCls, nCls);
			warpReduce(sh_rCls, nCls);
			if (threadIdx.x == 0) atomicAdd(&gstats->numClauses, nCls);
		}

		__global__ void cnt_lits(CNF* cnf, GSTATS* gstats)
		{
			uint32* sh_rLits = SharedMemory<uint32>();
			uint32 tid = global_tx_off();
			uint32 nLits = 0;
			while (tid < cnf->size()) {
				SCLAUSE& c1 = cnf->clause(tid);
				if (c1.original() || c1.learnt()) nLits += c1.size();
				uint32 off = tid + blockDim.x;
				if (off < cnf->size()) {
					SCLAUSE& c2 = cnf->clause(off);
					if (c2.original() || c2.learnt()) nLits += c2.size();
				}
				tid += stride_x_off();
			}
			loadShared(sh_rLits, nLits, cnf->size());
			sharedReduce(sh_rLits, nLits);
			warpReduce(sh_rLits, nLits);
			if (threadIdx.x == 0) atomicAdd(&gstats->numLits, nLits);
		}

		__global__ void cnt_cls_lits(CNF* cnf, GSTATS* gstats)
		{
			uint32* sh_rCls = SharedMemory<uint32>();
			uint32* sh_rLits = sh_rCls + blockDim.x;
			uint32 tid = global_tx_off();
			uint32 nCls = 0;
			uint32 nLits = 0;
			while (tid < cnf->size()) {
				SCLAUSE& c1 = cnf->clause(tid);
				if (c1.original() || c1.learnt()) nCls++, nLits += c1.size();
				uint32 off = tid + blockDim.x;
				if (off < cnf->size()) {
					SCLAUSE& c2 = cnf->clause(off);
					if (c2.original() || c2.learnt()) nCls++, nLits += c2.size();
				}
				tid += stride_x_off();
			}
			loadShared(sh_rCls, nCls, sh_rLits, nLits, cnf->size());
			sharedReduce(sh_rCls, nCls, sh_rLits, nLits);
			warpReduce(sh_rCls, nCls, sh_rLits, nLits);
			if (threadIdx.x == 0) {
				atomicAdd(&gstats->numClauses, nCls);
				atomicAdd(&gstats->numLits, nLits);
			}
		}

		__global__ void ve_k(CNF* cnf, OT* ot, cuVecU* pVars, cuVecU* units, cuVecU* resolved)
		{
			uint32 tx = threadIdx.x;
			uint32 tid = global_tx();
			__shared__ uint32 outs[BLVE * SH_MAX_BVE_OUT];
			while (tid < pVars->size()) {
				uint32& x = (*pVars)[tid];
				assert(x);
				assert(!ELIMINATED(x));
				uint32 p = V2L(x), n = NEG(p);
				OL& poss = (*ot)[p], &negs = (*ot)[n];
				uint32 pOrgs = poss.size(), nOrgs = negs.size();
				bool elim = false;
				// pure-literal elimination
				if (!pOrgs || !nOrgs) {
					toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
					elim = true;
				}
				else {
					assert(pOrgs && nOrgs);
					// Equiv/NOT-gate Reasoning
					if (find_equ_gate(p, pOrgs, nOrgs, *cnf, poss, negs, units, resolved)) elim = true;
					// AND-gate Reasoning
					else if (nOrgs < SH_MAX_BVE_OUT && find_ao_gate(n, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// OR-gate Reasoning
					else if (pOrgs < SH_MAX_BVE_OUT && find_ao_gate(p, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// ITE-gate Reasoning
					else if (find_ite_gate(p, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT])) 
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					else if (find_ite_gate(n, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// XOR-gate Reasoning
					else if (find_xor_gate(p, pOrgs + nOrgs, dc_limits[3], *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// n-by-m resolution
					else if (resolve(x, pOrgs, nOrgs, *cnf, poss, negs, units, resolved, &outs[tx * SH_MAX_BVE_OUT], false)) elim = true;
				}
				if (elim) x |= MELTING_MASK;
				tid += stride_x();
			}
		}

		__global__ void in_ve_k(CNF* cnf, OT* ot, cuVecU* pVars, cuVecU* units, cuVecU* resolved)
		{
			uint32 tx = threadIdx.x;
			uint32 tid = global_tx();
			__shared__ uint32 outs[BLVE * SH_MAX_BVE_OUT];
			while (tid < pVars->size()) {
				uint32& x = (*pVars)[tid];
				assert(x);
				assert(!ELIMINATED(x));
				uint32 p = V2L(x), n = NEG(p);
				OL& poss = (*ot)[p], &negs = (*ot)[n];
				uint32 pOrgs = 0, nOrgs = 0;
				countOrgs(*cnf, poss, pOrgs), countOrgs(*cnf, negs, nOrgs);
				bool elim = false;
				// pure-literal elimination
				if (!pOrgs || !nOrgs) {
					toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
					elim = true;
				}
				else {
					assert(pOrgs && nOrgs);
					// Equiv/NOT-gate Reasoning
					if (find_equ_gate(p, pOrgs, nOrgs, *cnf, poss, negs, units, resolved)) elim = true;
					// AND-gate Reasoning
					else if (nOrgs < SH_MAX_BVE_OUT && find_ao_gate(n, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// OR-gate Reasoning
					else if (pOrgs < SH_MAX_BVE_OUT && find_ao_gate(p, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// ITE-gate Reasoning
					else if (find_ite_gate(p, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					else if (find_ite_gate(n, pOrgs + nOrgs, *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// XOR-gate Reasoning
					else if (find_xor_gate(p, pOrgs + nOrgs, dc_limits[3], *cnf, *ot, units, resolved, &outs[tx * SH_MAX_BVE_OUT]))
						toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved), elim = true;
					// n-by-m resolution
					else if (resolve(x, pOrgs, nOrgs, *cnf, poss, negs, units, resolved, &outs[tx * SH_MAX_BVE_OUT], false)) elim = true;
				}
				if (elim) x |= MELTING_MASK;
				tid += stride_x();
			}
		}

		__global__ void in_ve_k_1(CNF* cnf, OT* ot, cuVecU* pVars, cuVecU* units, cuVecU* resolved, uint32* type, uint32* rpos, S_REF* rref)
		{
			uint32 tid = global_tx();
			uint32* outs = SharedMemory<uint32>();
			while (tid < pVars->size()) {
				uint32& x = (*pVars)[tid];
				assert(x);
				assert(!ELIMINATED(x));
				uint32 p = V2L(x), n = NEG(p);
				OL& poss = (*ot)[p], & negs = (*ot)[n];
				uint32 pOrgs = 0, nOrgs = 0;
				countOrgs(*cnf, poss, pOrgs), countOrgs(*cnf, negs, nOrgs);
				// pure-literal elimination
				if (!pOrgs || !nOrgs) {
					toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
					type[tid] = 0, rref[tid] = 0, rpos[tid] = 0, x |= MELTING_MASK;
				}
				// Equiv/NOT-gate Reasoning
				else if (uint32 def = find_equ_gate(p, pOrgs, nOrgs, *cnf, poss, negs, resolved)) {
					substitute_single(p, def, *cnf, poss, negs, units);
					type[tid] = 0, rref[tid] = 0, rpos[tid] = 0, x |= MELTING_MASK;
				}
				else {
					assert(pOrgs && nOrgs);
					uint32 elimType = 0, nAddedCls, nAddedLits;
					// AND-gate Reasoning
					if (nOrgs < SH_MAX_BVE_OUT1 && find_ao_gate(n, pOrgs + nOrgs, *cnf, *ot, resolved, outs + threadIdx.x * SH_MAX_BVE_OUT1, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// OR-gate Reasoning
					else if (pOrgs < SH_MAX_BVE_OUT1 && find_ao_gate(p, pOrgs + nOrgs, *cnf, *ot, resolved, outs + threadIdx.x * SH_MAX_BVE_OUT1, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// ITE-gate Reasoning
					else if (find_ite_gate(p, pOrgs + nOrgs, *cnf, *ot, resolved, nAddedCls, nAddedLits) ||
						     find_ite_gate(n, pOrgs + nOrgs, *cnf, *ot, resolved, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// XOR-gate Reasoning
					else if (find_xor_gate(p, pOrgs + nOrgs, dc_limits[3], *cnf, *ot, resolved, outs + threadIdx.x * SH_MAX_BVE_OUT1, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// n-by-m resolution
					else if (resolve(x, pOrgs, nOrgs, *cnf, poss, negs, resolved, nAddedCls, nAddedLits, false)) elimType = RES_MASK;
					if (!nAddedCls)  // eliminated without resolvents
						type[tid] = 0, rref[tid] = 0, rpos[tid] = 0, x |= MELTING_MASK;
					else if (elimType) { // can be eliminated with resolvents in next phase
						assert(nAddedLits >= nAddedCls);
						assert(nAddedCls < (ADDED_MASK / 4));
						type[tid] = (elimType | nAddedCls);
						rpos[tid] = nAddedCls, rref[tid] = (nAddedLits - nAddedCls) + dc_nbuckets * nAddedCls;
					}
					else  // cannot be eliminated
						type[tid] = 0, rref[tid] = 0, rpos[tid] = 0;
				}
				tid += stride_x();
			}
		}

		__global__ void ve_k_1(CNF* cnf, OT* ot, cuVecU* pVars, cuVecU* units, cuVecU* resolved, uint32* type, uint32* rpos, S_REF* rref)
		{
			uint32 tid = global_tx();
			uint32* outs = SharedMemory<uint32>();
			while (tid < pVars->size()) {
				uint32& x = (*pVars)[tid];
				assert(x);
				assert(!ELIMINATED(x));
				uint32 p = V2L(x), n = NEG(p);
				OL& poss = (*ot)[p], & negs = (*ot)[n];
				uint32 pOrgs = poss.size(), nOrgs = negs.size();
				// pure-literal elimination
				if (!pOrgs || !nOrgs) {
					toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
					type[tid] = 0, rref[tid] = 0, rpos[tid] = 0, x |= MELTING_MASK;
				}
				// Equiv/NOT-gate Reasoning
				else if (uint32 def = find_equ_gate(p, pOrgs, nOrgs, *cnf, poss, negs, resolved)) {
					substitute_single(p, def, *cnf, poss, negs, units);
					type[tid] = 0, rref[tid] = 0, rpos[tid] = 0, x |= MELTING_MASK;
				}
				else {
					assert(pOrgs && nOrgs);
					uint32 elimType = 0, nAddedCls, nAddedLits;
					// AND-gate Reasoning
					if (nOrgs < SH_MAX_BVE_OUT1 && find_ao_gate(n, pOrgs + nOrgs, *cnf, *ot, resolved, outs + threadIdx.x * SH_MAX_BVE_OUT1, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// OR-gate Reasoning
					else if (pOrgs < SH_MAX_BVE_OUT1 && find_ao_gate(p, pOrgs + nOrgs, *cnf, *ot, resolved, outs + threadIdx.x * SH_MAX_BVE_OUT1, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// ITE-gate Reasoning
					else if (find_ite_gate(p, pOrgs + nOrgs, *cnf, *ot, resolved, nAddedCls, nAddedLits) ||
						     find_ite_gate(n, pOrgs + nOrgs, *cnf, *ot, resolved, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// XOR-gate Reasoning
					else if (find_xor_gate(p, pOrgs + nOrgs, dc_limits[3], *cnf, *ot, resolved, outs + threadIdx.x * SH_MAX_BVE_OUT1, nAddedCls, nAddedLits)) {
						if (nAddedCls) saveResolved(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						else toblivion(p, pOrgs, nOrgs, *cnf, poss, negs, resolved);
						elimType = AOIX_MASK;
					}
					// n-by-m resolution
					else if (resolve(x, pOrgs, nOrgs, *cnf, poss, negs, resolved, nAddedCls, nAddedLits, false)) elimType = RES_MASK;
					if (!nAddedCls)  // eliminated without resolvents
						type[tid] = 0, rref[tid] = 0, rpos[tid] = 0, x |= MELTING_MASK;
					else if (elimType) { // can be eliminated with resolvents in next phase
						assert(nAddedLits >= nAddedCls);
						assert(nAddedCls < (ADDED_MASK / 4));
						type[tid] = (elimType | nAddedCls);
						rpos[tid] = nAddedCls, rref[tid] = (nAddedLits - nAddedCls) + dc_nbuckets * nAddedCls;
					}
					else  // cannot be eliminated
						type[tid] = 0, rref[tid] = 0, rpos[tid] = 0;
				}
				tid += stride_x();
			}
		}

		__global__ void ve_k_2(CNF* cnf, OT* ot, cuVecU* pVars, cuVecU* units, uint32* type, uint32* rpos, S_REF* rref)
		{
			uint32 tid = global_tx();
			uint32* outs = SharedMemory<uint32>();
			while (tid < pVars->size()) {
				uint32& x = (*pVars)[tid];
				assert(x);
				uint32 elimType = RECOVERTYPE(type[tid]);
				if (elimType) {
					assert(!ELIMINATED(x));
					uint32 p = V2L(x), nAddedCls = RECOVERADDED(type[tid]), added_pos = rpos[tid];
					S_REF added_ref = rref[tid];
					assert(nAddedCls);
					if (IS_RES(elimType))
						resolve_x(x, nAddedCls, added_pos, added_ref, *cnf, (*ot)[p], (*ot)[NEG(p)], units, outs + threadIdx.x * SH_MAX_BVE_OUT2);
					else
						assert(IS_AOIX(elimType)), substitute_x(x, nAddedCls, added_pos, added_ref, *cnf, (*ot)[p], (*ot)[NEG(p)], units, outs + threadIdx.x * SH_MAX_BVE_OUT2);
					x |= MELTING_MASK;
				}
				tid += stride_x();
			}
		}

		__global__ void hse_k(CNF* cnf, OT* ot, cuVecU* pVars, cuVecU* units)
		{
			uint32 tid = global_tx();
			__shared__ uint32 sh_cls[BLHSE * SH_MAX_HSE_IN];
			while (tid < pVars->size()) {
				uint32 x = (*pVars)[tid];
				assert(x);
				assert(!ELIMINATED(x));
				uint32 p = V2L(x), n = NEG(p);
				if ((*ot)[p].size() <= dc_limits[0] && (*ot)[n].size() <= dc_limits[0])
					subsume_x(p, *cnf, (*ot)[p], (*ot)[n], units, sh_cls + threadIdx.x * SH_MAX_HSE_IN);
				tid += stride_x();
			}
		}

		__global__ void bce_k(CNF* cnf, OT* ot, cuVecU* pVars)
		{
			uint32 tid = global_tx();
			__shared__ uint32 sh_cls[BLBCE * SH_MAX_BCE_IN];
			while (tid < pVars->size()) {
				uint32 x = (*pVars)[tid];
				assert(x);
				assert(!ELIMINATED(x));
				uint32 p = V2L(x), n = NEG(p);
				if ((*ot)[p].size() <= dc_limits[1] && (*ot)[n].size() <= dc_limits[1])
					blocked_x(x, *cnf, (*ot)[p], (*ot)[n], sh_cls + threadIdx.x * SH_MAX_BCE_IN);
				tid += stride_x();
			}
		}

		__global__ void ere_k(CNF* cnf, OT* ot, cuVecU* pVars)
		{
			uint32 gid = global_ty();
			uint32* smem = SharedMemory<uint32>();
			while (gid < pVars->size()) {
				uint32 v = pVars->at(gid);
				assert(v);
				assert(!ELIMINATED(v));
				uint32 p = V2L(v), n = NEG(p);
				OL& poss = (*ot)[p], & negs = (*ot)[n];
				// do merging and apply forward equality check (on-the-fly) over resolvents
				if (poss.size() <= dc_limits[2] && negs.size() <= dc_limits[2]) {
					for (S_REF* i = poss; i != poss.end(); i++) {
						SCLAUSE& pos = (*cnf)[*i];
						if (pos.deleted()) continue;
						for (S_REF* j = negs; j != negs.end(); j++) {
							SCLAUSE& neg = (*cnf)[*j];
							if (neg.deleted() || (pos.size() + neg.size() - 2) > SH_MAX_ERE_OUT) continue;
							uint32* m_c = smem + threadIdx.y * SH_MAX_ERE_OUT; // shared memory for resolvent
							int m_len = 0;
							if ((m_len = merge_ere(v, pos, neg, m_c)) > 1) {
								CL_ST type;
								if (pos.learnt() || neg.learnt()) type = LEARNT;
								else type = ORIGINAL;
								forward_equ(*cnf, *ot, m_c, m_len, type);
							}
						}
					}
				}
				gid += stride_y();
			}
		}
		//==============================================//
		//          ParaFROST Wrappers/helpers          //
		//==============================================//
		void initLimits(cuLimit culimit)
		{
			CHECK(cudaMemcpyToSymbol(dc_limits, &culimit.limits, sizeof(uint32) * NLIMITS, 0, cudaMemcpyHostToDevice));
		}
		void copyIf(uint32* dest, CNF* src, GSTATS* gstats)
		{
			if (profile_gpu) cutimer->start();
			reset_stats << <1, 1 >> > (gstats);
			uint32 nBlocks = std::min((inf.nClauses + BLOCK1D - 1) / BLOCK1D, maxGPUTereads / BLOCK1D);
			copy_if_k << <nBlocks, BLOCK1D >> > (dest, src, gstats);
			if (profile_gpu) cutimer->stop(), cutimer->vo += cutimer->gpuTime();
			LOGERR("Copying literals failed");
			syncAll();
		}
		void calcScores(VARS* vars, uint32* hist)
		{
			if (profile_gpu) cutimer->start();
			uint32 nBlocks = std::min((inf.maxVar + BLOCK1D - 1) / BLOCK1D, maxGPUTereads / BLOCK1D);
			assign_scores << <nBlocks, BLOCK1D >> > (vars->eligible, vars->scores, hist, inf.maxVar);
			if (profile_gpu) cutimer->stop(), cutimer->vo += cutimer->gpuTime();
			LOGERR("Assigning scores failed");
			syncAll();
		}
		void calcScores(VARS* vars, uint32* hist, OT* ot)
		{
			if (profile_gpu) cutimer->start();
			uint32 nBlocks = std::min((inf.maxVar + BLOCK1D - 1) / BLOCK1D, maxGPUTereads / BLOCK1D);
			assign_scores << <nBlocks, BLOCK1D >> > (vars->eligible, vars->scores, hist, ot, inf.maxVar);
			if (profile_gpu) cutimer->stop(), cutimer->vo += cutimer->gpuTime();
			LOGERR("Assigning scores failed");
			syncAll();
		}
		void countMelted(LIT_ST* vstate)
		{
			inf.n_del_vars_after = 0;
			for (uint32 v = 1; v <= inf.maxVar; v++)
				if (vstate[v] == MELTED)
					inf.n_del_vars_after++;
			assert(inf.n_del_vars_after >= inf.maxMelted);
			inf.n_del_vars_after -= inf.maxMelted;
			inf.maxMelted += inf.n_del_vars_after;
		}
		void countFinal(CNF* cnf, GSTATS* gstats, LIT_ST* vstate)
		{
			reset_stats << <1, 1 >> > (gstats);
			uint32 cnf_sz = inf.nClauses + (inf.nClauses >> 2);
			uint32 nBlocks = std::min((cnf_sz + (BLOCK1D << 1) - 1) / (BLOCK1D << 1), maxGPUTereads / (BLOCK1D << 1));
			uint32 smemSize = BLOCK1D * sizeof(uint32);
			cnt_cls << <nBlocks, BLOCK1D, smemSize >> > (cnf, gstats);
			if (unified_access || sync_always) {
				LOGERR("Final clause counting failed");
				syncAll();
			}
			countMelted(vstate);
			GSTATS hstats;
			CHECK(cudaMemcpy(&hstats, gstats, sizeof(GSTATS), cudaMemcpyDeviceToHost));
			inf.n_cls_after = hstats.numClauses;
		}
		void countCls(CNF* cnf, GSTATS* gstats)
		{
			reset_stats << <1, 1 >> > (gstats);
			uint32 cnf_sz = inf.nClauses;
			uint32 nBlocks = std::min((cnf_sz + (BLOCK1D << 1) - 1) / (BLOCK1D << 1), maxGPUTereads / (BLOCK1D << 1));
			uint32 smemSize = BLOCK1D * sizeof(uint32);
			cnt_cls << <nBlocks, BLOCK1D, smemSize >> > (cnf, gstats);
			GSTATS hstats;
			CHECK(cudaMemcpy(&hstats, gstats, sizeof(GSTATS), cudaMemcpyDeviceToHost));
			inf.n_cls_after = hstats.numClauses;
		}
		void countLits(CNF* cnf, GSTATS* gstats)
		{
			reset_stats << <1, 1 >> > (gstats);
			uint32 cnf_sz = inf.nClauses;
			uint32 nBlocks = std::min((cnf_sz + (BLOCK1D << 1) - 1) / (BLOCK1D << 1), maxGPUTereads / (BLOCK1D << 1));
			uint32 smemSize = BLOCK1D * sizeof(uint32);
			cnt_lits << <nBlocks, BLOCK1D, smemSize >> > (cnf, gstats);
			GSTATS hstats;
			CHECK(cudaMemcpy(&hstats, gstats, sizeof(GSTATS), cudaMemcpyDeviceToHost));
			inf.n_lits_after = hstats.numLits;
		}
		void countAll(CNF* cnf, GSTATS* gstats)
		{
			reset_stats << <1, 1 >> > (gstats);
			uint32 cnf_sz = inf.nClauses + (inf.nClauses >> 1);
			uint32 nBlocks = std::min((cnf_sz + (BLOCK1D << 1) - 1) / (BLOCK1D << 1), maxGPUTereads / (BLOCK1D << 1));
			uint32 smemSize = BLOCK1D * (sizeof(uint32) + sizeof(uint32));
			cnt_cls_lits << <nBlocks, BLOCK1D, smemSize >> > (cnf, gstats);
			GSTATS hstats;
			CHECK(cudaMemcpy(&hstats, gstats, sizeof(GSTATS), cudaMemcpyDeviceToHost));
			inf.n_cls_after = hstats.numClauses;
			inf.n_lits_after = hstats.numLits;
		}
		void evalReds(CNF* cnf, GSTATS* gstats, LIT_ST* vstate)
		{
			reset_stats << <1, 1 >> > (gstats);
			uint32 cnf_sz = inf.nClauses + (inf.nClauses >> 1);
			uint32 nBlocks1 = std::min((cnf_sz + (BLOCK1D << 1) - 1) / (BLOCK1D << 1), maxGPUTereads / (BLOCK1D << 1));
			uint32 smemSize1 = BLOCK1D * sizeof(uint32) * 2;
			cnt_reds << <nBlocks1, BLOCK1D, smemSize1 >> > (cnf, gstats);
			countMelted(vstate);
			GSTATS hstats;
			CHECK(cudaMemcpy(&hstats, gstats, sizeof(GSTATS), cudaMemcpyDeviceToHost)); // avoids unified memory migration on large scale
			inf.n_cls_after = hstats.numClauses;
			inf.n_lits_after = hstats.numLits;
		}
		void cuMemSetAsync(addr_t mem, const Byte& val, const size_t& size)
		{
			uint32 nBlocks = std::min(uint32((size + BLOCK1D - 1) / BLOCK1D), maxGPUTereads / BLOCK1D);
			memset_k<Byte> << <nBlocks, BLOCK1D >> > (mem, val, size);
			if (sync_always) {
				LOGERR("CUDA memory set failed");
				syncAll();
			}
		}
		void prepareCNFAsync(CNF* cnf, const cudaStream_t& _s)
		{
			assert(inf.nClauses);
			if (profile_gpu) cutimer->start(_s);
			uint32 nBlocks = std::min((inf.nClauses + BLOCK1D - 1) / BLOCK1D, maxGPUTereads / BLOCK1D);
			prep_cnf_k << <nBlocks, BLOCK1D, 0, _s >> > (cnf);
			if (profile_gpu) cutimer->stop(_s), cutimer->sig += cutimer->gpuTime();
			if (sync_always) {
				LOGERR("Signature calculation failed");
				syncAll();
			}
		}
		void reduceOTAsync(CNF* cnf, OT* ot, const bool& p)
		{
			assert(cnf != NULL);
			assert(ot != NULL);
			if (profile_gpu) cutimer->start();
			uint32 nBlocks = std::min(uint32((inf.nDualVars + BLOCK1D - 1) / BLOCK1D), maxGPUTereads / BLOCK1D);
			reduce_ot << <nBlocks, BLOCK1D >> > (cnf, ot);
			if (p || sync_always) {
				LOGERR("Occurrence table reduction failed");
				syncAll();
				if (p) {
					PFLRULER('=', 30);
					PFLOG0("\toccurrence table");
					ot->print();
					PFLRULER('=', 30);
				}
			}
			if (profile_gpu) cutimer->stop(), cutimer->rot += cutimer->gpuTime();
		}
		void createOTAsync(CNF* cnf, OT* ot, const bool& p)
		{
			assert(cnf != NULL);
			assert(ot != NULL);
			if (profile_gpu) cutimer->start();
			uint32 rstGridSize = std::min(uint32((inf.nDualVars + BLOCK1D - 1) / BLOCK1D), maxGPUTereads / BLOCK1D);
			reset_ot_k << <rstGridSize, BLOCK1D >> > (ot);
			uint32 otGridSize = std::min((inf.nClauses + BLOCK1D - 1) / BLOCK1D, maxGPUTereads / BLOCK1D);
			create_ot_k << <otGridSize, BLOCK1D >> > (cnf, ot);
			if (p || sync_always) {
				LOGERR("Occurrence table creation failed");
				syncAll();
				assert(ot->accViolation());
				if (p) {
					PFLRULER('=', 30);
					PFLOG0("\toccurrence table");
					ot->print();
					PFLRULER('=', 30);
				}
			}
			if (profile_gpu) cutimer->stop(), cutimer->cot += cutimer->gpuTime();
		}
		void sortOTAsync(CNF* cnf, OT* ot, VARS* vars, cudaStream_t* streams)
		{
			assert(cnf != NULL);
			assert(ot != NULL);
			assert(vars->numPVs);
			uint32 nBlocks = std::min((vars->numPVs + BLSORT - 1) / BLSORT, maxGPUTereads / BLSORT);
			cudaStream_t s1, s2;
			if (profile_gpu) s1 = s2 = 0, cutimer->start();
			else s1 = streams[0], s2 = streams[1];
			sort_ot_p << <nBlocks, BLSORT, 0, s1 >> > (cnf, ot, vars->pVars);
			sort_ot_n << <nBlocks, BLSORT, 0, s2 >> > (cnf, ot, vars->pVars);
			if (sync_always) {
				LOGERR("Sorting OT failed");
				syncAll();
			}
			if (profile_gpu) cutimer->stop(), cutimer->sot += cutimer->gpuTime();
		}
		void veAsync(CNF* cnf, OT* ot, VARS* vars, cudaStream_t* streams, cuMM& cumm, const cuHist& cuhist, const bool& in)
		{
			assert(vars->numPVs);
			if (profile_gpu) cutimer->start();
			if (!atomic_ve) {
				uint32 cs_size = cumm.pinnedCNF()->size();
				S_REF data_size = cumm.pinnedCNF()->data().size;
				S_REF* rref = cuhist.d_segs;
				uint32* type = cuhist.d_hist, *rpos = type + inf.maxVar;
				// Phase-1
				uint32 smSize1 = (BLVE1 * SH_MAX_BVE_OUT1) * sizeof(uint32);
				#if VE_DBG
				putchar('\n');
				if (in) in_ve_k_1 << <1, 1, smSize1 >> > (cnf, ot, vars->pVars, vars->units, vars->resolved, type, rpos, rref);
				else	   ve_k_1 << <1, 1, smSize1 >> > (cnf, ot, vars->pVars, vars->units, vars->resolved, type, rpos, rref);
				#else
				uint32 nBlocks1 = std::min((vars->numPVs + BLVE1 - 1) / BLVE1, maxGPUTereads / BLVE1);
				if (in) in_ve_k_1 << <nBlocks1, BLVE1, smSize1 >> > (cnf, ot, vars->pVars, vars->units, vars->resolved, type, rpos, rref);
				else	   ve_k_1 << <nBlocks1, BLVE1, smSize1 >> > (cnf, ot, vars->pVars, vars->units, vars->resolved, type, rpos, rref);
				#endif
				// Phase-2
				size_t tb1 = 0, tb2 = 0;
				DeviceScan::ExclusiveScan(NULL, tb1, rpos, rpos, Sum(), cs_size, vars->numPVs), assert(tb1 <= cumm.literalsCap());
				DeviceScan::ExclusiveScan(NULL, tb2, rref, rref, Sum(), data_size, vars->numPVs), assert(tb2 <= cumm.scatterCap());
				LOGERR("BVE Phase-1 failed"); sync(); //sync phase-1
				void* ts1 = cuhist.d_lits, *ts2 = cumm.scatter();
				DeviceScan::ExclusiveScan(ts1, tb1, rpos, rpos, Sum(), cs_size, vars->numPVs, streams[0]);
				DeviceScan::ExclusiveScan(ts2, tb2, rref, rref, Sum(), data_size, vars->numPVs, streams[1]);
				uint32 nBlocks2 = std::min((vars->numPVs + BLVE2 - 1) / BLVE2, maxGPUTereads / BLVE2);
				uint32 smSize2 = (BLVE2 * SH_MAX_BVE_OUT2) * sizeof(uint32);
				LOGERR("BVE Phase-2 failed"); sync(streams[0]), sync(streams[1]); // sync phase-2
				#if VE_DBG
				putchar('\n');
				ve_k_2 << <1, 1, smSize2 >> > (cnf, ot, vars->pVars, vars->units, type, rpos, rref);
				#else
				// Phase-3
				ve_k_2 << <nBlocks2, BLVE2, smSize2 >> > (cnf, ot, vars->pVars, vars->units, type, rpos, rref);
				#endif
			}
			else {
				#if VE_DBG
				putchar('\n');
				if (in) in_ve_k << <1, 1 >> > (cnf, ot, vars->pVars, vars->units, vars->resolved);
				else	   ve_k << <1, 1 >> > (cnf, ot, vars->pVars, vars->units, vars->resolved);
				#else
				uint32 nBlocks1 = std::min((vars->numPVs + BLVE - 1) / BLVE, maxGPUTereads / BLVE);
				if (in)	in_ve_k << <nBlocks1, BLVE >> > (cnf, ot, vars->pVars, vars->units, vars->resolved);
				else	   ve_k << <nBlocks1, BLVE >> > (cnf, ot, vars->pVars, vars->units, vars->resolved);
				#endif
			}
			if (profile_gpu) cutimer->stop(), cutimer->ve += cutimer->gpuTime();
			LOGERR("BVE Elimination failed"); syncAll();
		}
		void hseAsync(CNF* cnf, OT* ot, VARS* vars)
		{
			assert(vars->numPVs);
			if (profile_gpu) cutimer->start();
#if SS_DBG
			putchar('\n');
			hse_k << <1, 1 >> > (cnf, ot, vars->pVars, vars->units);
#else
			uint32 nBlocks = std::min((vars->numPVs + BLHSE - 1) / BLHSE, maxGPUTereads / BLHSE);
			hse_k << <nBlocks, BLHSE >> > (cnf, ot, vars->pVars, vars->units);
#endif
			if (profile_gpu) cutimer->stop(), cutimer->hse += cutimer->gpuTime();
			if (sync_always) { 
				LOGERR("HSE Elimination failed");
				syncAll();
			}
		}
		void bceAsync(CNF* cnf, OT* ot, VARS* vars)
		{
			assert(vars->numPVs);
			if (profile_gpu) cutimer->start();
			uint32 nBlocks = std::min((vars->numPVs + BLBCE - 1) / BLBCE, maxGPUTereads / BLBCE);
			bce_k << <nBlocks, BLBCE >> > (cnf, ot, vars->pVars);
			if (profile_gpu) cutimer->stop(), cutimer->bce += cutimer->gpuTime();
			if (sync_always) {
				LOGERR("BCE Elimination failed");
				syncAll();
			}
		}
		void ereAsync(CNF* cnf, OT* ot, VARS* vars)
		{
			assert(vars->numPVs);
			if (profile_gpu) cutimer->start();
			dim3 block2D(devProp.warpSize, devProp.warpSize), grid2D(1, 1, 1);
			grid2D.y = std::min((vars->numPVs + block2D.y - 1) / block2D.y, maxGPUTereads / block2D.y);
			uint32 smemSize = devProp.warpSize * SH_MAX_ERE_OUT * sizeof(uint32);
			ere_k << <grid2D, block2D, smemSize >> > (cnf, ot, vars->pVars);
			if (profile_gpu) cutimer->stop(), cutimer->ere += cutimer->gpuTime();
			if (sync_always) {
				LOGERR("ERE Elimination failed");
				syncAll();
			}
		}

	}
}
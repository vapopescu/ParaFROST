/***********************************************************************[pfsimp.cpp]
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

#include "pfsimp.h"

using namespace pFROST;
using namespace SIGmA;

void ParaFROST::createOT(const bool& rst)
{
	if (opts.profile_simp) timer.pstart();

	// reset ot
	if (rst) {
		workerPool.doWorkForEach((size_t)1, (size_t)(inf.maxVar + 1), [this](size_t i) {
			uint32 p = V2L(i);
			ot[p].clear();
			ot[NEG(p)].clear();
		});

		workerPool.join();
	}

	// create ot
	workerPool.doWorkForEach((size_t)0, (size_t)scnf.size(), [this](size_t i) {
		SCLAUSE& c = *scnf[i];
		if (c.learnt() || c.original()) {
			assert(c.size());
			for (int k = 0; k < c.size(); k++) {
				assert(c[k] > 1);
				ot[c[k]].lock();
				ot[c[k]].push(scnf[i]);
				ot[c[k]].unlock();
			}
		}
	});

	workerPool.join();
	if (opts.profile_simp) timer.pstop(), timer.cot += timer.pcpuTime();
}

void ParaFROST::reduceOL(OL& ol)
{
	if (ol.empty()) return;
	int n = 0;
	for (int i = 0; i < ol.size(); i++) {
		if (ol[i]->deleted()) continue;
		ol[n++] = ol[i];
	}
	ol.resize(n);
}

void ParaFROST::reduceOT()
{
	if (opts.profile_simp) timer.pstart();

	workerPool.doWorkForEach((uint32)1, inf.maxVar, [&](uint32 v) {
		uint32 p = V2L(v), n = NEG(p);
		reduceOL(ot[p]);
		reduceOL(ot[n]);
	});
	workerPool.join();

	if (opts.profile_simp) timer.pstop(), timer.rot += timer.pcpuTime();
}

void ParaFROST::sortOT(bool partial)
{
	if (opts.profile_simp) timer.pstart();

	if (!partial && opts.ce_en) {
		workerPool.doWorkForEach((uint32)1, inf.maxVar, [this](uint32 v) {
			assert(v);
			uint32 p = V2L(v), n = NEG(p);
			OL& poss = ot[p], & negs = ot[n];
			std::sort(poss.data(), poss.data() + poss.size(), CNF_CMP_ABS());
			std::sort(negs.data(), negs.data() + negs.size(), CNF_CMP_ABS());
		});
		workerPool.join();
	}
	else if (partial && !opts.ce_en) {
		workerPool.doWorkForEach((uint32)0, PVs.size(), [this](uint32 i) {
			uint32& v = PVs[i];
			assert(v);
			uint32 p = V2L(v), n = NEG(p);
			OL& poss = ot[p], & negs = ot[n];
			std::sort(poss.data(), poss.data() + poss.size(), CNF_CMP_KEY());
			std::sort(negs.data(), negs.data() + negs.size(), CNF_CMP_KEY());
		});
		workerPool.join();
	}

	if (opts.profile_simp) timer.pstop(), timer.sot += timer.pcpuTime();
}

void ParaFROST::extract(const BCNF& cnf)
{
	for (uint32 i = 0; i < cnf.size(); i++) {
		CLAUSE& c = cm[cnf[i]];
		if (c.deleted()) continue;
		newSClause(new SCLAUSE(c));
	}
}

void ParaFROST::awaken(const bool& strict)
{ 
	assert(conflict == NOREF);
	assert(cnfstate == UNSOLVED);
	assert(sp->propagated == trail.size());
	initSimp();
	if (stats.sigmifications && strict) reduceTop(strict);
	if (orgs.empty()) { sigState = AWAKEN_FAIL; return; }
	// alloc simplifier memory 
	PFLOGN2(2, " Allocating memory..");
	size_t numCls = maxClauses(), numLits = maxLiterals();
	size_t ot_cap = inf.nDualVars * sizeof(OL) + numLits * sizeof(S_REF);
	size_t ig_cap = inf.nDualVars * sizeof(IG);
	size_t scnf_cap = numCls * sizeof(S_REF) + numLits * sizeof(uint32);
	if (!checkMem("ot", ot_cap) || !checkMem("ig", ig_cap) || !checkMem("scnf", scnf_cap))
	{ sigState = SALLOC_FAIL; return; }
	ot.resize(inf.nDualVars), ig.resize(inf.nDualVars), scnf.resize(numCls);
	PFLENDING(2, 5, "(%.1f MB used)", double(ot_cap + scnf_cap) / MBYTE);
	// append clauses to scnf
	PFLOGN2(2, " Extracting clauses to simplifying CNF..");
	printStats(1, '-', CGREEN0), inf.nClauses = inf.nLiterals = 0;
	wt.clear(true);
	extract(orgs), orgs.clear(true);
	extract(learnts), learnts.clear(true);
	// resize cnf & clean old database
	scnf.resize(inf.nClauses);
	cm.destroy();
	PFLENDING(2, 5, "(%d clauses extracted)", inf.nClauses);
	PFLMEMCALL(this, 2);
	return;
}

void ParaFROST::sigmify()
{
	/********************************/
	/*		Getting ready...        */
	/********************************/
	if (!opts.phases && !(opts.all_en || opts.ere_en)) return;
	backtrack();
	if (BCP()) { cnfstate = UNSAT; return; }
	shrink(orgs), shrink(learnts);
	/********************************/
	/*         awaken sigma         */
	/********************************/
	timer.stop(), timer.solve += timer.cpuTime(), timer.start();
	awaken();
	if (cnfstate == UNSAT || sigState == AWAKEN_FAIL) return;
	if (sigState == SALLOC_FAIL) return;
	if (!interrupted()) {
		int64 before, diff;
		/********************************/
		/*      V/C Eliminations        */
		/********************************/
		assert(!phase && !mu_inc);
		before = inf.nLiterals, diff = INT64_MAX;
		while (true) {
			// Stage 1
			resizeCNF();
			createOT();
			int p = prop();
			if (p > 0) { PFLREDALL(this, 2, "BCP Reductions"); }
			else if (p < 0) break;

			// Stage 2
			IGR();
			if (cnfstate == UNSAT) return;

			// Stage 3
			sortOT(false);
			CE();

			// Stage 4
			if (!LCVE()) break;
			sortOT(true);
			if (stop(diff)) { ERE(); break; }
			HSE(), BVE(), BCE();

			// Cleanup
			countAll(), filterPVs();
			inf.nClauses = inf.n_cls_after, inf.nLiterals = inf.n_lits_after;
			diff = before - inf.nLiterals, before = inf.nLiterals;
			phase++, mu_inc++;
			mu_inc += phase == opts.phases;
		}
		/********************************/
		/*          Write Back          */
		/********************************/
		assert(sp->propagated == trail.size());
		if (interrupted()) killSolver();
		occurs.clear(true), ot.clear(true);
		countFinal();
		shrinkSimp(), assert(inf.nClauses == scnf.size());
		stats.sigmifications++;
		lrn.elim_lastmarked = lrn.elim_marked;
		if (opts.aggr_cnf_sort) std::stable_sort(scnf.data(), scnf.data() + scnf.size(), CNF_CMP_KEY());
		if (inf.maxFrozen > sp->simplified) stats.n_forced += inf.maxFrozen - sp->simplified;
		if (satisfied() || !inf.nClauses)
			cnfstate = SAT, printStats(1, 'p', CGREEN);
		else {
			if (maxInactive() > opts.map_min) map(true);
			else assert(!mapped), newBeginning();
			sigmaDelay();
		}
	}

	timer.stop(), timer.simp += timer.cpuTime();
	if (!opts.solve_en) killSolver();
	timer.start();
}

void ParaFROST::shrinkSimp() {
	if (opts.profile_simp) timer.pstart();

	std::vector<SCNF> partialSCNF(workerPool.count());
	for (uint32 i = 0; i < partialSCNF.size(); i++) {
		partialSCNF[i].reserve(scnf.size() * 2 / workerPool.count());
	}

	workerPool.doWorkForEach((size_t)0, scnf.size(), [&](size_t i) {
		S_REF c = scnf[i];
		uint32 ti = workerPool.getID();
		assert(ti >= 0);

		if (c->deleted()) removeClause(c);
		else partialSCNF[ti].push(c);
	});
	workerPool.join();

	uint32 n = 0;
	for (uint32 i = 0; i < partialSCNF.size(); i++) {
		for (uint32 j = 0; j < partialSCNF[i].size(); j++) {
			scnf[n++] = partialSCNF[i][j];
		}
		partialSCNF[i].clear(true);
	}
	scnf.resize(n);

	if (opts.profile_simp) timer.pstop(), timer.gc += timer.pcpuTime();
}

void ParaFROST::newBeginning() {
	assert(opts.sigma_en || opts.sigma_live_en);
	assert(wt.empty());
	assert(orgs.empty());
	assert(learnts.empty());
	assert(inf.maxVar > vmap.numVars());
	if (!mapped) assert(vmap.empty()), sp->lockMelted(inf.maxVar);
	cm.init(scnf.size());
	inf.nLiterals = inf.nLearntLits = 0;
	for (S_REF* s = scnf; s != scnf.end(); s++) newClause(**s);
	assert(size_t(orgs.size() + learnts.size()) == scnf.size());
	inf.nOrgCls = orgs.size();
	inf.nOrgLits = inf.nLiterals;
	scnf.clear(true);
	wt.resize(mapped ? V2L(vmap.size()) : inf.nDualVars);
	rebuildWT(opts.priorbins_en);
	printStats(1, 'p', CGREEN);
}

inline void	ParaFROST::sigmaDelay() {
	if (opts.sigma_live_en) {
		// update inprocessing trigger (inspired by Cadical) 
		// but we decrease phases too
		double current_inc = scale(opts.sigma_inc * (phase + 1.0));
		lrn.sigma_conf_max = nConflicts + current_inc;
		PFLOG2(2, " inprocessing limit increased to %lld conflicts by a weight of %.2f", lrn.sigma_conf_max, current_inc);
		if (opts.phases > 2) {
			opts.phases--;
			PFLOG2(2, " inprocessing phases decreased to %d", opts.phases);
		}
	}
}
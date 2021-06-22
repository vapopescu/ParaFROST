/***********************************************************************[pfelim.cpp]
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
#include "scc_wrapper.h"

using namespace pFROST;
using namespace SIGmA;

int ParaFROST::prop()
{
	std::mutex m;
	std::condition_variable cvWorker, cvMaster;
	int working = workerPool.count();
	bool terminate = false;

	nForced = sp->propagated;
	workerPool.doWork([&] {
		uint32 assign;
		while (true) {
			{
				std::unique_lock<std::mutex> lock(m);
				std::function<bool()> condition = [&] { return sp->propagated < trail.size() || terminate || cnfstate == UNSAT; };
				if (!condition()) {
					working--;
					cvMaster.notify_one();
					cvWorker.wait(lock, condition);
					working++;
				}
				if (terminate) break;
				else if (cnfstate == UNSAT) {
					working--;
					cvMaster.notify_one();
					break;
				}
				assign = trail[sp->propagated++];
			}

			assert(assign > 1);
			uint32 f_assign = FLIP(assign);
			// remove satisfied
			for (int i = 0; i < ot[assign].size(); i++) ot[assign][i]->markDeleted();
			// reduce unsatisfied
			for (int i = 0; i < ot[f_assign].size(); i++) {
				S_REF c = ot[f_assign][i];
				//c->print();
				c->lock();
				assert(c->size());
				if (c->deleted() || propClause(c, f_assign)) { c->unlock(); continue; } // clause satisfied
				// clause is unit or conflict
				// Note: attach & strengthen don't check for conflict before enqueue
				if (c->size() == 0) {
					c->unlock();
					std::unique_lock<std::mutex> lock(m);
					cnfstate = UNSAT;
					break;
				}
				if (c->size() == 1) {
					assert(**c > 1);
					std::unique_lock<std::mutex> lock(m);
					if (unassigned(**c)) {
						enqueueOrg(**c);
						cvWorker.notify_one();
					}
					else {
						cnfstate = UNSAT;
						c->unlock();
						break;
					}
				}
				c->unlock();
			}
			// delete assign lists
			ot[assign].clear(true), ot[f_assign].clear(true);
		}
	});

	std::unique_lock<std::mutex> lock(m);
	cvMaster.wait(lock, [&working] { return working == 0; });
	terminate = true;
	cvWorker.notify_all();
	lock.unlock();
	workerPool.join();

	if (cnfstate == UNSAT) return -1;
	nForced = sp->propagated - nForced;
	assert(nForced >= 0);
	int retval = nForced;
	return retval;
}

void ParaFROST::IGR()
{
	if (phase == 0 && opts.igr_en) {
		if (interrupted()) killSolver();
		PFLOGN2(2, " Reasoning on the implication graph..");
		if (opts.profile_simp) timer.pstart();
		bool done = false;

		workerPool.doWorkForEach((uint32)0, inf.nDualVars, [this](uint32 i) {
			ig[i].clear();
		});

		workerPool.join();

		while (!done) {
			// Propagate boolean constraints
			std::mutex propagateMutex;
			if (sp->propagated < trail.size()) {
				if (prop() < 0) break;
			}

			// Initialize IG based on original binary clauses.
			workerPool.doWorkForEach((size_t)0, scnf.size(), [this](size_t i) {
				S_REF c = scnf[i];
				if (!c->deleted() && c->size() == 2) {
					uint32 lit1 = c->lit(0), lit2 = c->lit(1);
					ig[lit1].lock(); ig[lit1].insertParent(FLIP(lit2), c); ig[lit1].unlock();
					ig[lit2].lock(); ig[lit2].insertParent(FLIP(lit1), c); ig[lit2].unlock();
					ig[FLIP(lit1)].lock(); ig[FLIP(lit1)].insertChild(lit2, c); ig[FLIP(lit1)].unlock();
					ig[FLIP(lit2)].lock(); ig[FLIP(lit2)].insertChild(lit1, c); ig[FLIP(lit2)].unlock();
				}
			});
			workerPool.join();

			// SCC equivalence reduction
			bool sccScan = true;
			while (sccScan) {
				SCCWrapper wrapper;
				wrapper.setNumThreads(opts.worker_count);
				wrapper.setMethod(SCC_UFSCC);
				wrapper.setGraph(ig);

				node_t* scc = wrapper.getSCC();
				std::atomic<uint32> sccCount = 0;
				std::atomic<bool> newEdge = false;

				workerPool.doWorkForEach((uint32)1, inf.maxVar, [&](uint32 v) {
					const uint32 lit = V2L(v);
					scc[FLIP(lit)] = FLIP(scc[lit]);
				});
				workerPool.join();

				workerPool.doWorkForEach((uint32)1, inf.maxVar, [&](uint32 v) {
					const uint32 lit = V2L(v);
					const uint32& repLit = scc[lit];

					if (lit == repLit) sccCount++;
					else {
						bool n = false;
						n |= node_reduce(lit, repLit, ot, ig);
						n |= node_reduce(FLIP(lit), FLIP(repLit), ot, ig);
						if (n) newEdge = true;
						sp->vstate[v] = MELTED, v = 0;
					}
				});
				workerPool.join();
				delete[] scc;
				if (!newEdge) sccScan = false;
			}

			// TODO: reset SCC ancestor nodes.

			// Explore IG
			uVec1D exploreQueue;
			std::mutex exploreMutex;
			std::condition_variable exploreWorker, exploreMaster;
			std::atomic<uint32> exploreIdx = 0;
			int exploreWorking = workerPool.count();
			bool exploreTerminate = false;
			exploreQueue.reserve(inf.nDualVars);

			workerPool.doWorkForEach((uint32)2, inf.nDualVars, [&](uint32 lit) {
				bool explore = true;
				Vec<Edge>& cs = ig[lit].children();

				for (int i = 0; i < cs.size(); i++) {
					if (!ig[cs[i].first].isExplored()) {
						explore = false;
						break;
					}
				}

				if (explore) { std::unique_lock lock(exploreMutex); exploreQueue.push(lit); }
			});
			workerPool.join();

			workerPool.doWork([&] {
				uint32 lit = 0;
				while (true) {
					{
						std::unique_lock lock(exploreMutex);
						std::function<bool()> condition = [&] { return exploreIdx < exploreQueue.size() || exploreTerminate; };
						if (!condition()) {
							exploreWorking--;
							exploreMaster.notify_one();
							exploreWorker.wait(lock, condition);
							exploreWorking++;
						}
						if (exploreTerminate) break;
						lit = exploreQueue[exploreIdx++];
					}

					ig[lit].lockRead();

					Vec<Edge>& ps = ig[lit].parents();
					Vec<Edge>& cs = ig[lit].children();
					uVec1D& ds = ig[lit].descendants();

					// If the node got reduced, check the reference.
					while (ig[lit].isReduced()) {
						uint32 newLit = ig[lit].descendants()[0];
						ig[lit].unlockRead();
						lit = newLit;
						ig[lit].lockRead();
					}

					// Early return. Nothing left to do.
					if (ig[lit].isExplored()) {
						ig[lit].unlockRead();
						continue;
					}

					// Check if all children are explored.
					bool childrenExplored = true;
					for (uint32 i = 0; i < cs.size(); i++) {
						if (!cs[i].second->deleted()) {
							uint32 c = cs[i].first;
							ig[c].lockRead();
							if (!ig[c].isExplored()) {
								childrenExplored = false;
								ig[c].unlockRead();
								break;
							}
							ig[c].unlockRead();
						}
					}
					ig[lit].unlockRead();

					// Cannot procede if not all children are explored.
					if (!childrenExplored) continue;

					ig[lit].lock();
					for (uint32 i = 0; i < cs.size(); i++) {
						if (!cs[i].second->deleted()) {
							uint32 c = cs[i].first;
							ig[c].lockRead();
							bool redundant = false;

							// Remove redundant edges.
							for (uint32 j = 0; j < ds.size(); j++) {
								if (ds[j] < c) continue;
								else if (ds[j] == c) {
									cs[i].second->markDeleted();
									redundant = true;
									break;
								}
								else break;
							}

							// Gather descendants.
							if (!redundant) {
								uVec1D grandchildren;
								auto& gcs = ig[c].children();
								for (uint32 i = 0; i < gcs.size(); i++) {
									if (!gcs[i].second->deleted()) {
										grandchildren.push(gcs[i].first);
									}
								}

								ig[lit].descendants().unionize(grandchildren);
								ig[lit].descendants().unionize(ig[c].descendants());
							}

							ig[c].unlockRead();
						}
					}

					// Check if literal is failed.
					uint32 flipLit = FLIP(lit);
					bool failed = false;
					for (uint32 i = 0; i < ds.size(); i++) {
						if (flipLit == ds[i]) {
							ig[lit].unlock();
							ig[flipLit].lockRead();
							propagateMutex.lock();

							{
								uVec1D& units = ig[flipLit].descendants();
								for (uint32 j = 0; j < units.size(); j++) {
									if (unassigned(units[j])) enqueueOrg(units[j]);
								}
							}

							{
								Vec<Edge>& units = ig[flipLit].children();
								for (uint32 j = 0; j < units.size(); j++) {
									if (unassigned(units[j].first)) enqueueOrg(units[j].first);
								}
							}

							if (unassigned(flipLit)) enqueueOrg(flipLit);

							propagateMutex.unlock();
							ig[flipLit].unlockRead();
							failed = true;
							break;
						}
					}

					if (failed) continue;

					// Queue parents for exploration.
					if (!ps.empty()) {
						std::unique_lock lock(exploreMutex);
						for (uint32 i = 0; i < ps.size(); i++) {
							if (!ps[i].second->deleted()) {
								exploreQueue.push(ps[i].first);
								exploreWorker.notify_one();
							}
						}
					}

					ig[lit].markExplored();
					ig[lit].unlock();
				}
			});

			std::unique_lock<std::mutex> lock(exploreMutex);
			exploreMaster.wait(lock, [&] { return exploreWorking == 0 || exploreTerminate; });
			exploreTerminate = true;
			exploreWorker.notify_all();
			lock.unlock();
			workerPool.join();

			// Exit condition
			if (trail.size() == sp->propagated && exploreIdx == exploreQueue.size()) done = true;
		}

		/*for (uint32 i = 2; i < inf.nDualVars; i++) {
			printf("ig[%d]:\n", i);
			printf("\tparents: ");
			for (uint32 j = 0; j < ig[i].parents().size(); j++) {
				printf("%d, ", ig[i].parents()[j].first);
			}
			printf("\n\tchildren: ");
			for (uint32 j = 0; j < ig[i].children().size(); j++) {
				printf("%d, ", ig[i].children()[j].first);
			}
			printf("\n\tdescendants: ");
			for (uint32 j = 0; j < ig[i].descendants().size(); j++) {
				printf("%d, ", ig[i].descendants()[j]);
			}
			printf("\n");
		}*/

		if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime();
		PFLDONE(2, 5);
		//PFLOG2(2, " Number of SCCs in IG is %d.", (uint32)sccCount);
		PFLREDALL(this, 2, "IGR Reductions");
	}
}

void ParaFROST::CE()
{
	if (phase == 0 && opts.ce_en && (opts.hse_en || opts.bce_en)) {
		if (interrupted()) killSolver();
		PFLOGN2(2, "  Eliminating clauses..");
		if (opts.profile_simp) timer.pstart();

		workerPool.doWorkForEach((size_t)0, scnf.size(), (size_t)64, [this](size_t i) {
			clause_elim(scnf[i], ot, ig);
		});

		workerPool.join();
		if (opts.profile_simp) timer.pstop(), timer.ce += timer.pcpuTime();
		PFLDONE(2, 5);
		PFLREDALL(this, 2, "Clause Reductions");
	}
}

void ParaFROST::bve()
{
	if (interrupted()) killSolver();
	if (opts.profile_simp) timer.pstart();
	std::atomic<uint32> ti = 0;
	std::vector<uVec1D> resolved(PVs.size());
	std::vector<SCNF> new_res(PVs.size());
	OL resolvents;

	workerPool.doWork([&] {
		Lits_t out_c;
		out_c.reserve(INIT_CAP);

		while (true) {
			uint32 i = ti++;
			if (i >= PVs.size()) break;
			uint32 v = PVs[i];
			assert(v);
			assert(sp->vstate[v] == ACTIVE);
			uint32 p = V2L(v), n = NEG(p);
			OL& poss = ot[p], & negs = ot[n];
			int pOrgs = 0, nOrgs = 0;
			countOrgs(poss, pOrgs), countOrgs(negs, nOrgs);
			// pure-literal
			if (!pOrgs || !nOrgs) {
				toblivion(p, pOrgs, nOrgs, poss, negs, resolved[i]);
				sp->vstate[v] = MELTED, v = 0;
			}
			else {
				assert(pOrgs && nOrgs);
				out_c.clear();
				uint32 def;
				// Equiv/NOT-gate Reasoning
				if (def = find_BN_gate(p, poss, negs)) {
					saveResolved(p, pOrgs, nOrgs, poss, negs, resolved[i]);
					substitute_single(p, def, poss, negs);
					sp->vstate[v] = MELTED, v = 0;
				}
				// AND-gate Reasoning
				else if (find_AO_gate(n, pOrgs + nOrgs, ot, out_c, new_res[i])) {
					toblivion(p, pOrgs, nOrgs, poss, negs, resolved[i]);
					sp->vstate[v] = MELTED, v = 0;
				}
				// OR-gate Reasoning
				else if (find_AO_gate(p, pOrgs + nOrgs, ot, out_c, new_res[i])) {
					toblivion(p, pOrgs, nOrgs, poss, negs, resolved[i]);
					sp->vstate[v] = MELTED, v = 0;
				}
				// ITE-gate Reasoning
				else if (find_ITE_gate(p, pOrgs + nOrgs, ot, out_c, new_res[i])) {
					toblivion(p, pOrgs, nOrgs, poss, negs, resolved[i]);
					sp->vstate[v] = MELTED, v = 0;
				}
				else if (find_ITE_gate(n, pOrgs + nOrgs, ot, out_c, new_res[i])) {
					toblivion(p, pOrgs, nOrgs, poss, negs, resolved[i]);
					sp->vstate[v] = MELTED, v = 0;
				}
				// XOR-gate Reasoning
				else if (find_XOR_gate(p, pOrgs + nOrgs, ot, out_c, new_res[i])) {
					toblivion(p, pOrgs, nOrgs, poss, negs, resolved[i]);
					sp->vstate[v] = MELTED, v = 0;
				}
				// n-by-m resolution
				else if (resolve_x(v, pOrgs, nOrgs, poss, negs, out_c, new_res[i], false)) {
					toblivion(p, pOrgs, nOrgs, poss, negs, resolved[i]);
					sp->vstate[v] = MELTED, v = 0;
				}
			}
		}
	});

	workerPool.join();
	uint32 resLit = 0;
	for (uint32 i = 0; i < PVs.size(); i++) {
		resLit += resolved[i].size();
	}

	uint32 resNum = 0;
	for (uint32 i = 0; i < PVs.size(); i++) {
		resNum += new_res[i].size();
	}

	model.resolved.reserve(model.resolved.size() + resLit + 1);
	for (uint32 i = 0; i < PVs.size(); i++) {
		for (int j = 0; j < resolved[i].size(); j++) {
			model.resolved.push(resolved[i][j]);
		}
		model.resolved.push(resLit);

		for (int j = 0; j < new_res[i].size(); j++) {
			S_REF c = new_res[i][j];
			newResolvent(c);
			resolvents.push(c);
		}

		resolved[i].clear(true);
		new_res[i].clear(true);
	}

	if (opts.profile_simp) timer.pstop(), timer.ve += timer.pcpuTime();
}

void ParaFROST::VE()
{
	if (opts.ve_en) {
		PFLOGN2(2, "  Eliminating variables..");
		bve();
		PFLDONE(2, 5);
		PFLREDALL(this, 2, "VE Reductions");
	}
}

void ParaFROST::HSE()
{
	if (!opts.ce_en && (opts.hse_en || opts.ve_plus_en)) {
		if (interrupted()) killSolver();
		PFLOGN2(2, "  Eliminating (self)-subsumptions..");
		if (opts.profile_simp) timer.pstart();
		std::atomic<uint32> ti = 0;

		workerPool.doWork([&] {
			while (true) {
				uint32 i = ti++;
				if (i >= PVs.size()) break;
				uint32 v = PVs[i];
				assert(v);
				assert(sp->vstate[v] == ACTIVE);
				uint32 p = V2L(v), n = NEG(p);
				if (ot[p].size() <= opts.hse_limit && ot[n].size() <= opts.hse_limit)
					self_sub_x(p, ot[p], ot[n]);
			}
		});

		workerPool.join();
		if (opts.profile_simp) timer.pstop(), timer.hse += timer.pcpuTime();
		PFLDONE(2, 5);
		PFLREDALL(this, 2, "HSE Reductions");
	}
}

void ParaFROST::BCE()
{
	if (!opts.ce_en && opts.bce_en) {
		if (interrupted()) killSolver();
		PFLOGN2(2, " Eliminating blocked clauses..");
		if (opts.profile_simp) timer.pstart();
		std::atomic<uint32> ti = 0;

		workerPool.doWork([&] {
			while (true) {
				uint32 i = ti++;
				if (i >= PVs.size()) break;
				uint32 v = PVs[i];
				if (!v) continue;
				uint32 p = V2L(v), n = NEG(p);
				if (ot[p].size() <= opts.bce_limit && ot[n].size() <= opts.bce_limit)
					blocked_x(v, ot[n], ot[p]);
			}
		});

		workerPool.join();
		if (opts.profile_simp) timer.pstop(), timer.bce += timer.pcpuTime();
		PFLDONE(2, 5);
		PFLREDALL(this, 2, "BCE Reductions");
	}
}

void ParaFROST::ERE()
{
	if (!opts.ere_en) return;
	if (interrupted()) killSolver();
	PFLOGN2(2, " Eliminating redundances..");
	if (opts.profile_simp) timer.pstart();
	std::atomic<uint32> ti = 0;

	workerPool.doWork([&] {
		Lits_t m_c;
		m_c.reserve(INIT_CAP);

		while (true) {
			uint32 n = ti++;
			if (n >= PVs.size()) break;
			assert(PVs[n]);
			uint32 p = V2L(PVs[n]);
			OL& poss = ot[p], & negs = ot[NEG(p)];

			if (ot[p].size() <= opts.ere_limit && ot[n].size() <= opts.ere_limit) {
				// do merging and apply forward equality check (on-the-fly) over resolvents
				for (int i = 0; i < poss.size(); i++) {
					if (poss[i]->deleted()) continue;
					for (int j = 0; j < negs.size(); j++) {
						if (negs[j]->deleted() || (poss[i]->size() + negs[j]->size() - 2) > MAX_ERE_OUT) continue;
						if (merge_ere(PVs[n], poss[i], negs[j], m_c)) {
							CL_ST type;
							if (poss[i]->learnt() || negs[j]->learnt()) type = LEARNT;
							else type = ORIGINAL;
							if (m_c.size() > 1) forward_equ(m_c, ot, type);
						}
					}
				}
			}
		}
	});

	workerPool.join();
	if (opts.profile_simp) timer.pstop(), timer.ere += timer.pcpuTime();
	PFLDONE(2, 5);
	PFLREDCL(this, 2, "ERE Reductions");
}

bool ParaFROST::propClause(S_REF c, const uint32& f_assign)
{
	uint32 sig = 0;
	int n = 0;
	bool check = false;
	for (int k = 0; k < c->size(); k++) {
		uint32 lit = c->lit(k);
		if (lit != f_assign) {
			if (isTrue(lit)) return true;
			(*c)[n++] = lit;
			sig |= MAPHASH(lit);
		}
		else check = true;
	}
	assert(check);
	assert(n == c->size() - 1);
	assert(c->hasZero() < 0);
	assert(c->isSorted());
	c->set_sig(sig);
	c->pop();
	return false;
}

void ParaFROST::strengthen(S_REF c, const uint32& self_lit)
{
	uint32 sig = 0;
	int n = 0;
	bool check = false;
	for (int k = 0; k < c->size(); k++) {
		uint32 lit = c->lit(k);
		if (lit != self_lit) {
			(*c)[n++] = lit;
			sig |= MAPHASH(lit);
		}
		else check = true;
	}
	assert(check);
	assert(n == c->size() - 1);
	assert(c->hasZero() < 0);
	assert(c->isSorted());
	c->set_sig(sig);
	c->pop();
	if (opts.proof_en) {
		wrProof('a');
		wrProof(*c, n);
		wrProof(0);
	}
	if (n == 1 && unassigned(**c)) enqueueOrg(**c);
	else if (n > 1 && c->learnt()) bumpShrunken(c);
}

inline void ParaFROST::bumpShrunken(S_REF c)
{
	assert(c->learnt());
	assert(c->size() > 1);
	int old_lbd = c->lbd();
	if (old_lbd <= opts.lbd_tier1) return; // always keep Tier1 value
	int new_lbd = std::min(c->size() - 1, old_lbd);
	if (new_lbd >= old_lbd) return;
	c->set_lbd(new_lbd);
	c->set_usage(USAGET3);
	PFLCLAUSE(4, (*c), " Bumping shrunken clause with (lbd:%d, usage:%d) ", new_lbd, c->usage());
}
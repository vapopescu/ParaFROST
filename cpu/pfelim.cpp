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

using namespace pFROST;
using namespace SIGmA;

int ParaFROST::prop(SCNF* bin_check)
{
	std::mutex m;
	std::condition_variable cv;
	int working = workerPool.count();
	nForced = sp->propagated;

	workerPool.doWork([&] {
		uint32 assign = 0;
		while (cnfstate == UNSOLVED) {
			{
				std::unique_lock<std::mutex> lock(m);
				working--;

				while (sp->propagated == trail.size()) {
					if (working == 0 || cnfstate == UNSAT) {
						cv.notify_all();
						return;
					}
					else cv.wait(lock);
				}

				if (cnfstate == UNSAT) break;
				working++;
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
						cv.notify_one();
					}
					else if (isFalse(**c)) {
						cnfstate = UNSAT;
						c->unlock();
						break;
					}
				}
				if (c->size() == 2 && bin_check != nullptr) {
					bin_check->lock();
					bin_check->push(c);
					bin_check->unlock();
				}
				c->unlock();
			}
			// delete assign lists
			ot[assign].clear(true), ot[f_assign].clear(true);
		}
	});
	workerPool.join();

	if (cnfstate == UNSAT) return -1;
	nForced = sp->propagated - nForced;
	assert(nForced >= 0);
	int retval = nForced;
	nForced = 0;
	return retval;
}

void ParaFROST::IGR()
{
	if (phase == 0 && opts.igr_en) {
		if (interrupted()) killSolver();
		PFLOGN2(2, " Reasoning on the implication graph..");
		if (opts.profile_simp) timer.pstart();

		// Initialize IG based on original binary clauses.
		workerPool.doWorkForEach((size_t)0, scnf.size(), [this](size_t i) {
			S_REF c = scnf[i];
			if (c->size() == 2 /*&& c->original()*/ && !c->deleted()) append_ig_edge(c, ig);
		});
		workerPool.join();

		if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[0] += timer.pcpuTime();

		workerPool.doWorkForEach((uint32)0, ig.size(), [this](uint32 i) {
			ig[i].sortEdges();
		});
		workerPool.join();

		SCCWrapper sccWrapper;
		sccWrapper.setNumThreads(opts.worker_count);
		sccWrapper.setMethod(SCC_UFSCC);
		sccWrapper.setGraph(ig);

		bool done = false;
		int hbrRetries = opts.hbr_max > 0 ? opts.hbr_max : -1;

		if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[1] += timer.pcpuTime();

		while (!done && cnfstate == UNSOLVED) {
			if (opts.profile_simp) timer.pstart();

			// Propagate boolean constraints
			std::mutex propagateMutex;
			SCNF bin_check;
			bin_check.reserve(INIT_CAP);

			if (sp->propagated < trail.size()) {
				if (prop(&bin_check) < 0) break;
			}

			if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[2] += timer.pcpuTime(), timer.pstart();

			workerPool.doWorkForEach((size_t)0, bin_check.size(), [&](size_t i) {
				S_REF c = bin_check[i];
				if (!c->deleted() && c->size() == 2) insert_ig_edge(c, ig);
			});
			workerPool.join();

			// SCC equivalence reduction
			uVec1D resetQueue;
			resetQueue.reserve(inf.nDualVars);
			bool sccScan = true;
			std::atomic<bool> sccReset = false;

			if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[3] += timer.pcpuTime();

			while (sccScan) {
				if (opts.profile_simp) timer.pstart();

				// Compute SCC for each node.
				node_t* scc = sccWrapper.getSCC();
				std::atomic<uint32> sccCount = 0;
				std::atomic<bool> newEdge = false;

				workerPool.doWorkForEach((uint32)1, inf.maxVar, [&](uint32 v) {
					const uint32 lit = V2L(v);
					scc[FLIP(lit)] = FLIP(scc[lit]);
				});
				workerPool.join();

				if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[4] += timer.pcpuTime(), timer.pstart();

				// Replace each node with its SCC representative.
				workerPool.doWorkForEach((uint32)1, inf.maxVar, [&](uint32 v) {
					const uint32 lit = V2L(v);
					const uint32 repLit = scc[lit];

					assert(repLit > 1);
					assert(repLit < inf.nDualVars);

					if (lit == repLit) sccCount++;
					else {
						bool n = false;
						OL newUnit;

						n |= node_reduce(lit, repLit, ot, ig, newUnit);
						n |= node_reduce(FLIP(lit), FLIP(repLit), ot, ig, newUnit);
						if (n) newEdge = true;
						//sp->vstate[v] = MELTED;

						for (int i = 0; i < newUnit.size(); i++) {
							uint32 unit = newUnit[i]->lit(0);

							propagateMutex.lock();
							if (unassigned(unit)) enqueueOrg(unit);
							else if (isFalse(unit)) cnfstate = UNSAT;
							propagateMutex.unlock();

							sccReset = true;
						}
						newUnit.clear(true);

						resetQueue.lock();
						resetQueue.push(lit);
						resetQueue.unlock();
					}
				});
				workerPool.join();

				delete[] scc;
				if (!newEdge || sccReset) sccScan = false;

				if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[5] += timer.pcpuTime();
			}

			if (sccReset) { continue; }

			if (opts.profile_simp) timer.pstart();

			// Reset SCC ancestor nodes.
			std::mutex resetMutex;
			std::condition_variable resetCV;
			std::atomic<uint32> resetIdx = 0;
			int resetWorking = workerPool.count();

			workerPool.doWork([&] {
				uint32 lit = 0;
				while (true) {
					if (lit == 0) {
						std::unique_lock lock(resetMutex);
						resetWorking--;

						while (resetIdx == resetQueue.size()) {
							if (resetWorking == 0) {
								resetCV.notify_all();
								return;
							}
							else resetCV.wait(lock);
						}

						resetWorking++;
						lit = resetQueue[resetIdx++];
					}

					ig[lit].lock();
					uint32 newLit = 0;

					if (ig[lit].isExplored()) {
						// Reset node.
						ig[lit].markUnexplored();

						// Queue parents for reset.
						Vec<Edge>& ps = ig[lit].parents();
						if (!ps.empty()) {
							if (ps.size() > 1) {
								std::unique_lock lock(resetMutex);
								for (uint32 i = 1; i < ps.size(); i++) {
									if (!ps[i].second->deleted()) {
										resetQueue.push(ps[i].first);
										resetCV.notify_one();
									}
								}
							}
							newLit = ps[0].first;
						}
					}

					ig[lit].unlock();
					lit = newLit;
				}
			});
			workerPool.join();

			// Scan IG for exploration starting points.
			uVec1D exploreQueue;

			if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[6] += timer.pcpuTime(), timer.pstart();

			workerPool.doWorkForEach((uint32)2, inf.nDualVars, [&](uint32 lit) {
				if (!ig[lit].isExplored()) {
					bool explore = true;
					bool deadEnd = true;
					Vec<Edge>& cs = ig[lit].children();
					ig[lit].lockRead();

					for (uint32 i = 0; i < cs.size(); i++) {
						if (!cs[i].second->deleted()) {
							deadEnd = false;
							uint32& child = cs[i].first;

							ig[child].lockRead();
							if (!ig[child].isExplored()) {
								ig[child].unlockRead();
								explore = false;
								break;
							}
							ig[child].unlockRead();
						}
					}

					if (deadEnd && ig[lit].isOrphan()) {
						ig[lit].markExplored(); // nothing to do for this node
					}
					else if (explore) {
						exploreQueue.lock();
						exploreQueue.push(lit);
						exploreQueue.unlock();
					}

					ig[lit].unlockRead();
				}
			});
			workerPool.join();

			// Explore IG
			std::mutex exploreMutex;
			std::condition_variable exploreCV;
			std::atomic<uint32> exploreIdx = 0;
			std::atomic<bool> exploreTerminate = false;
			std::vector<SCNF> newClauses(workerPool.count());
			int exploreWorking = workerPool.count();
			exploreQueue.reserve(inf.nDualVars);

			if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[7] += timer.pcpuTime(), timer.pstart();

			workerPool.doWork([&] {
				uint32 lit = 0;
				uint32 ti = workerPool.getID();
				assert(ti >= 0);

				while (cnfstate == UNSOLVED || !exploreTerminate) {
					if (lit == 0) {
						std::unique_lock lock(exploreMutex);
						exploreWorking--;

						while (exploreIdx == exploreQueue.size()) {
							if (exploreWorking == 0 || cnfstate == UNSAT || exploreTerminate) {
								exploreTerminate = true;
								exploreCV.notify_all();
								break;
							}
							else exploreCV.wait(lock);
						}

						if (exploreTerminate) break;
						exploreWorking++;
						lit = exploreQueue[exploreIdx++];
					}

					ig[lit].lockRead();

					uint32 flipLit = FLIP(lit);
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
					if (ig[lit].isExplored()) { ig[lit].unlockRead(); lit = 0; continue; }

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
					if (!childrenExplored) { lit = 0; continue; }

					ig[lit].lock();
					for (uint32 i = 0; i < cs.size(); i++) {
						if (!cs[i].second->deleted()) {
							uint32 c = cs[i].first;
							ig[c].lockRead();
							bool redundant = false;

							// Remove redundant edges.
							/*for (uint32 j = 0; j < ds.size(); j++) {
								if (ds[j] < c) continue;
								else if (ds[j] == c) {
									cs[i].second->markDeleted();
									redundant = true;
									break;
								}
								else break;
							}*/

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
					bool failed = false;
					if (opts.fle_en) {
						for (uint32 i = 0; i < ds.size(); i++) {
							if (flipLit == ds[i]) {
								ig[lit].clear(true);
								ig[lit].markExplored();
								ig[lit].unlock();

								ig[flipLit].lockRead();
								propagateMutex.lock();

								if (cnfstate == UNSOLVED) {
									uVec1D& units = ig[flipLit].descendants();
									for (uint32 j = 0; j < units.size(); j++) {
										if (unassigned(units[j])) enqueueOrg(units[j]);
										else if (isFalse(units[j])) { cnfstate = UNSAT; exploreCV.notify_all(); }
									}
								}

								if (cnfstate == UNSOLVED) {
									Vec<Edge>& units = ig[flipLit].children();
									for (uint32 j = 0; j < units.size(); j++) {
										if (unassigned(units[j].first)) enqueueOrg(units[j].first);
										else if (isFalse(units[j].first)) { cnfstate = UNSAT; exploreCV.notify_all(); }
									}
								}

								if (unassigned(flipLit)) enqueueOrg(flipLit);
								else if (isFalse(flipLit)) { cnfstate = UNSAT; exploreCV.notify_all(); }

								propagateMutex.unlock();
								ig[flipLit].unlockRead();

								failed = true;
								break;
							}
						}

						if (failed) { lit = 0; continue; }
					}

					// Hyper-Binary-Resolution
					if (opts.hbr_en && hbrRetries != 0) {
						ig[lit].unlock();

						// Compute transitive closure
						uVec1D transClosure;
						ig[lit].lockRead();
						transClosure.reserve(cs.size() + ds.size() + 1);
						for (uint32 i = 0; i < cs.size(); i++) {
							if (!cs[i].second->deleted()) {
								transClosure.push(cs[i].first);
							}
						}
						transClosure.unionize(ds);
						transClosure.unionize(uVec1D({ lit }));
						ig[lit].unlockRead();

						// Compute propagation closure
						uVec1D propClosure, propQueue;
						uint32 propIdx = 0;
						propClosure.copyFrom(transClosure);
						propQueue.copyFrom(transClosure);

						while (propIdx < propQueue.size() && cnfstate == UNSOLVED) {
							uint32 assign = propQueue[propIdx++];
							uint32 f_assign = FLIP(assign);
							assert(assign > 1);

							// reduce unsatisfied
							for (int i = 0; i < ot[f_assign].size(); i++) {
								S_REF& c = ot[f_assign][i];
								if (c->deleted()) continue;
								uint32 unitLit = 0;

								for (int k = 0; k < c->size(); k++) {
									if (propClosure.contains(c->lit(k))) { unitLit = 1; break; }
									else if (!propClosure.contains(FLIP(c->lit(k)))) {
										if (unitLit <= 1) unitLit = c->lit(k);
										else { unitLit = 1; break; };
									}
								}

								if (unitLit == 0) {
									// conflict => failed literal
									propagateMutex.lock();
									if (unassigned(flipLit)) enqueueOrg(flipLit);
									else if (isFalse(flipLit)) { cnfstate = UNSAT; exploreCV.notify_all(); }
									propagateMutex.unlock();
									failed = true;
									break;
								}

								if (unitLit > 1) {
									propQueue.push(unitLit);
									propClosure.unionize(uVec1D({ unitLit }));
								}

								if (exploreTerminate) break;
							}

							if (exploreTerminate) break;
						}

						if (exploreTerminate || cnfstate == UNSAT) { lit = 0; continue; }

						// Compare the closures
						uint32 i = 0, j = 0;
						Lits_t out_c; out_c.reserve(2);

						while (i < propClosure.size() && j < transClosure.size()) {
							if (propClosure[i] == transClosure[j]) { i++; j++; }
							else if (propClosure[i] < transClosure[j]) {
								add_binary_clause(propClosure[i], flipLit, newClauses[ti], out_c);
								failed = true;
								i++;
							}
							else { assert(false); j++; }
						}

						while (i < propClosure.size()) {
							add_binary_clause(propClosure[i], flipLit, newClauses[ti], out_c);
							failed = true;
							i++;
						}

						if (failed) { hbrRetries--; exploreTerminate = true; exploreCV.notify_all(); break; }

						ig[lit].lock();
					}

					// Queue parents for exploration.
					uint32 newLit = 0;
					if (!ps.empty()) {
						if (ps.size() > 1) {
							std::unique_lock lock(exploreMutex);
							for (uint32 i = 1; i < ps.size(); i++) {
								if (!ps[i].second->deleted()) {
									exploreQueue.push(ps[i].first);
									exploreCV.notify_one();
								}
							}
						}
						newLit = ps[0].first;
					}

					ig[lit].markExplored();
					ig[lit].unlock();
					lit = newLit;
				}
			});
			workerPool.join();

			// Add new clauses to CNF
			for (uint32 i = 0; i < newClauses.size(); i++) {
				for (uint32 j = 0; j < newClauses[i].size(); j++) {
					S_REF& c = newClauses[i][j];
					newBinary(c);
					insert_ig_edge(c, ig);
					ot[c->lit(0)].push(c);
					ot[c->lit(1)].push(c);
				}
				newClauses[i].clear(true);
			}

			if (opts.profile_simp) timer.pstop(), timer.igr += timer.pcpuTime(), timer.igr_part[8] += timer.pcpuTime();

			// Exit condition
			if (trail.size() == sp->propagated && exploreIdx == exploreQueue.size()) done = true;
		}

		// Sanity check.
#ifdef IGR_DBG
		std::mutex printMutex;
		bool ok = true;
		workerPool.doWorkForEach((uint32)2, inf.nDualVars, [&](uint32 i) {
			if (!ig[i].isExplored()) {
				std::unique_lock lock(printMutex);
				printf("ig[%d]:\n", i);
				printf("\tparents: ");
				for (uint32 j = 0; j < ig[i].parents().size(); j++) {
					if (!ig[i].parents()[j].second->deleted()) {
						printf("%d, ", ig[i].parents()[j].first);
					}
				}
				printf("\n\tchildren: ");
				for (uint32 j = 0; j < ig[i].children().size(); j++) {
					if (!ig[i].children()[j].second->deleted()) {
						printf("%d, ", ig[i].children()[j].first);
					}
				}
				printf("\n\tdescendants: ");
				for (uint32 j = 0; j < ig[i].descendants().size(); j++) {
					printf("%d, ", ig[i].descendants()[j]);
				}
				printf("\n");
				ok = false;
			}
		});
		workerPool.join();
		assert(ok);
#endif

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

void ParaFROST::BVE()
{
	if (opts.ve_en) {
		if (interrupted()) killSolver();
		PFLOGN2(2, "  Eliminating variables..");
		if (opts.profile_simp) timer.pstart();

		std::vector<uVec1D> resolved(PVs.size());
		std::vector<SCNF> new_res(PVs.size());

		workerPool.doWorkForEach((uint32)0, PVs.size(), (uint32)1, [&](uint32 i) {
			uint32& v = PVs[i];
			assert(v);
			assert(sp->vstate[v] == ACTIVE);

			Lits_t out_c;
			out_c.reserve(INIT_CAP);
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
		});
		workerPool.join();

		uint32 resCount = 0;
		for (uint32 i = 0; i < PVs.size(); i++) {
			resCount += resolved[i].size();
		}

		model.resolved.reserve(model.resolved.size() + resCount + 1);
		for (uint32 i = 0; i < PVs.size(); i++) {
			for (uint32 j = 0; j < resolved[i].size(); j++) {
				model.resolved.push(resolved[i][j]);
			}
			model.resolved.push(resCount);

			for (int j = 0; j < new_res[i].size(); j++) {
				S_REF c = new_res[i][j];
				newResolvent(c);
			}

			resolved[i].clear(true);
			new_res[i].clear(true);
		}

		if (opts.profile_simp) timer.pstop(), timer.ve += timer.pcpuTime();
		PFLDONE(2, 5);
		PFLREDALL(this, 2, "BVE Reductions");
	}
}

void ParaFROST::HSE()
{
	if (!opts.ce_en && (opts.hse_en || opts.ve_plus_en)) {
		if (interrupted()) killSolver();
		PFLOGN2(2, "  Eliminating (self)-subsumptions..");
		if (opts.profile_simp) timer.pstart();

		workerPool.doWorkForEach((uint32)0, PVs.size(), (uint32)1, [&](uint32 i) {
			uint32 v = PVs[i];
			assert(v);
			assert(sp->vstate[v] == ACTIVE);
			uint32 p = V2L(v), n = NEG(p);
			if (ot[p].size() <= opts.hse_limit && ot[n].size() <= opts.hse_limit)
				self_sub_x(p, ot[p], ot[n]);
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

		workerPool.doWorkForEach((uint32)0, PVs.size(), (uint32)1, [&](uint32 i) {
			uint32 v = PVs[i];
			if (!v) return;
			uint32 p = V2L(v), n = NEG(p);
			if (ot[p].size() <= opts.bce_limit && ot[n].size() <= opts.bce_limit)
				blocked_x(v, ot[n], ot[p]);
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

	workerPool.doWorkForEach((uint32)0, PVs.size(), (uint32)1, [&](uint32 i) {
		uint32 v = PVs[i];
		assert(v);
		uint32 p = V2L(v);
		OL& poss = ot[p], & negs = ot[NEG(p)];
		Lits_t m_c;
		m_c.reserve(INIT_CAP);

		if (ot[p].size() <= opts.ere_limit && ot[NEG(p)].size() <= opts.ere_limit) {
			// do merging and apply forward equality check (on-the-fly) over resolvents
			for (int i = 0; i < poss.size(); i++) {
				if (poss[i]->deleted()) continue;
				for (int j = 0; j < negs.size(); j++) {
					if (negs[j]->deleted() || (poss[i]->size() + negs[j]->size() - 2) > MAX_ERE_OUT) continue;
					if (merge_ere(PVs[i], poss[i], negs[j], m_c)) {
						CL_ST type;
						if (poss[i]->learnt() || negs[j]->learnt()) type = LEARNT;
						else type = ORIGINAL;
						if (m_c.size() > 1) forward_equ(m_c, ot, type);
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
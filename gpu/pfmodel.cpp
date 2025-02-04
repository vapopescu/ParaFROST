/***********************************************************************[pfvec.h]
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

#include "pfmodel.h"

using namespace pFROST;
using namespace SIGmA;

void MODEL::extend(const LIT_ST* currValue, const uVec1D& vorg)
{
	uint32 updated = 0;
	value.resize(maxVar + 1, 0);
	for (uint32 v = 1; v <= maxVar; v++) {
		uint32 mlit = lits[v];
		if (mlit) {
			value[v] = currValue[mlit];
			updated++;
		}
	}
	PFLOG2(2, "");
	PFLOG2(2, " Extending model updated %d mapped values", updated);
	if (resolved.size()) {
		uint32 before = updated;
		uint32* x = resolved.end() - 1, k;
		uint32 witness, orgWitness = 0;
		while (x > resolved) {
			assert(*x);
			witness = 0;
			bool unsat = true;
			for (k = *x--; k > 1; k--, x--) {
				witness = *x;
				CHECKLIT(witness);
				orgWitness = V2DEC(vorg[ABS(witness)], SIGN(witness));
				if (satisfied(orgWitness)) { unsat = false; break; }
			}
			if (unsat) {
				if (!witness) {
					witness = *x;
					CHECKLIT(witness);
					orgWitness = V2DEC(vorg[ABS(witness)], SIGN(witness));
				}
				assert(orgWitness > 1);
				value[ABS(orgWitness)] = !SIGN(orgWitness);
				updated++;
			}
			x -= k;
		}
		PFLOG2(2, " Extending model with eliminated variables updated %d values", updated - before);
	}
	PFLOG2(2, "");
}

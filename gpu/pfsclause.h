/***********************************************************************[pfsclause.h]
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

#ifndef __SCLAUSE_
#define __SCLAUSE_

#include "pfcudefs.h"
#include "pfclause.h"

namespace pFROST {

	namespace SIGmA {
		/*****************************************************/
		/*  Usage:      abstract clause for GPU simplifier   */
		/*  Dependency:  none                                */
		/*****************************************************/
		typedef uint64 S_REF;
		#define GNOREF UINT64_MAX
		class SCLAUSE {
			CL_ST _st, _f, _a, _u;
			int _sz, _lbd;
			uint32 _sig;
			union { uint32 _lits[1]; };
		public:
			_PFROST_H_D_ S_REF		blockSize			() const { assert(_sz); return (_sz - 1) + (sizeof(*this) / sizeof(uint32)); }
			_PFROST_H_D_ size_t		capacity			() const { assert(_sz); return (size_t(_sz) - 1) * sizeof(uint32) + sizeof(*this); }
			_PFROST_H_D_			SCLAUSE				() { _st = ORIGINAL, _sz = 0, _sig = 0, _lbd = 0, _f = 0, _a = 0, _u = 0; }
			_PFROST_H_D_			SCLAUSE				(uint32* lits, const int& size) {
				_st = ORIGINAL, _sig = 0, _lbd = 0, _f = 0, _a = 0, _u = 0;
				_sz = size, copyLitsFrom(lits);
			}
			_PFROST_H_				SCLAUSE				(CLAUSE& src) {
				_sz = src.size(), _st = src.status();
				if (learnt()) { _lbd = src.lbd(), _u = src.usage(); }
				else { _lbd = 0, _u = 0; }
				_sig = 0, _f = 0, _a = 0;
				copyLitsFrom(src);
			}
			_PFROST_H_D_			SCLAUSE				(SCLAUSE& src) {
				assert(!src.deleted());
				_f = src.molten();
				_u = src.usage();
				_a = src.added();
				_st = src.status();
				_sig = src.sig();
				_lbd = src.lbd();
				_sz = src.size();
				copyLitsFrom(src);
			}
			_PFROST_H_D_ void		copyLitsFrom		(uint32* src) {
				assert(_sz);
				for (int k = 0; k < _sz; k++) {
					assert(src[k] > 1);
					_lits[k] = src[k];
				}
			}
			_PFROST_H_D_ void		resize				(const int& size) { _sz = size; }
			_PFROST_H_D_ void		push				(const uint32& lit) { _lits[_sz++] = lit; }
			_PFROST_H_D_ void		set_lbd				(const int& lbd) { _lbd = lbd; }
			_PFROST_H_D_ void		set_sig				(const uint32& sig) { _sig = sig; }
			_PFROST_H_D_ void		set_usage			(const CL_ST& usage) { _u = usage; }
			_PFROST_H_D_ void		set_status			(const CL_ST& status) { _st = status; }
			_PFROST_H_D_ uint32&	operator[]			(const int& i)		 { assert(i < _sz); return _lits[i]; }
			_PFROST_H_D_ uint32		operator[]			(const int& i) const { assert(i < _sz); return _lits[i]; }
			_PFROST_H_D_ uint32*	data				(const int& i = 0) { assert(i < _sz); return _lits + i; }
			_PFROST_H_D_ uint32*	end					() { return _lits + _sz; }
			_PFROST_H_D_ uint32		back				() { assert(_sz); return _lits[_sz - 1]; }
			_PFROST_H_D_ operator	uint32*				() { assert(_sz); return _lits; }
			_PFROST_H_D_ void		pop					() { _sz--; }
			_PFROST_H_D_ void		clear				() { _sz = 0; }
			_PFROST_H_D_ void		freeze				() { _f = 0; }
			_PFROST_H_D_ void		melt				() { _f = 1; }
			_PFROST_H_D_ void		markAdded			() { _a = 1; }
			_PFROST_H_D_ void		markDeleted			() { _st = DELETED; }
			_PFROST_H_D_ CL_ST		usage				() const { return _u; }
			_PFROST_H_D_ bool		molten				() const { return _f; }
			_PFROST_H_D_ bool		added				() const { return _a; }
			_PFROST_H_D_ bool		empty				() const { return !_sz; }
			_PFROST_H_D_ bool		original			() const { return _st & ORIGINAL; }
			_PFROST_H_D_ bool		deleted				() const { return _st & DELETED; }
			_PFROST_H_D_ bool		learnt				() const { return _st & LEARNT; }
			_PFROST_H_D_ CL_ST		status				() const { return _st; }
			_PFROST_H_D_ int		size				() const { return _sz; }
			_PFROST_H_D_ int		lbd					() const { return _lbd; }
			_PFROST_H_D_ uint32		sig					() const { return _sig; }
			_PFROST_H_D_ void		shareTo				(uint32* dest) {
				assert(_sz > 1);
				uint32* s = _lits, * e = s + _sz;
				while (s != e) *dest++ = *s++;
			}
			_PFROST_H_D_ bool		has					(const uint32& lit) const { // binary search
				assert(_sz);
				if (_sz == 2) {
					if (_lits[0] == lit || _lits[1] == lit) return true;
					else return false;
				}
				else {
					assert(isSorted());
					int low = 0, high = _sz - 1, mid;
					uint32 first = _lits[low], last = _lits[high];
					while (first <= lit && last >= lit) {
						mid = ((low + high) >> 1);
						uint32 m = _lits[mid];
						if (m < lit) first = _lits[low = mid + 1];
						else if (m > lit) last = _lits[high = mid - 1];
						else return true; // found
					}
					if (_lits[low] == lit) return true; // found
					else return false; // Not found
				}
			}
			_PFROST_H_D_ bool		isSorted			() const {
				for (int i = 0; i < _sz; i++)
					if (i > 0 && _lits[i] < _lits[i - 1])
						return false;
				return true;
			}
			_PFROST_H_D_ int		hasZero				() const {
				for (int i = 0; i < _sz; i++)
					if (_lits[i] == 0) 
						return i;
				return -1;
			}
			_PFROST_H_D_ void		print				() {
				printf("(");
				for (int l = 0; l < _sz; l++) {
					int lit = int(ABS(_lits[l]));
					lit = (SIGN(_lits[l])) ? -lit : lit;
					printf("%4d ", lit);
				}
				char st = 'U';
				if (deleted()) st = 'X';
				else if (added()) st = 'A';
				else if (original()) st = 'O';
				else if (learnt()) st = 'L';
				printf(") %c:%d, used=%d, lbd=%d, s=0x%X\n", st, molten(), usage(), _lbd, _sig);
			}
		};

	}
}

#endif
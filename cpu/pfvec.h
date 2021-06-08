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

#ifndef __VEC_
#define __VEC_

#include "pfralloc.h"
#include <cstdlib>
#include <limits>
#include <cassert>
#include <typeinfo>
#include <iostream>
#include <mutex>

#ifdef __GNUC__
#define __forceinline __attribute__((always_inline))
#endif

namespace pFROST {

	template<class T, class S = uint32>
	class Vec {
		T* _mem;
		S sz, cap, maxCap;
		std::mutex _m;

		bool check(const S& idx) const {
			if (idx >= sz) {
				std::cout << "Error - index is out of vector boundary (type: " << typeid(T).name() <<
					", idx: " << (long long)idx << ", sz:" << (long long)sz << std::endl;
				return false;
			}
			return true;
		}
	public:
		__forceinline			~Vec		() { clear(true); }
		__forceinline			Vec			() { init(); }
		__forceinline			Vec			(const Vec<T, S>& orig) { init(); copyFrom(orig); }
		__forceinline explicit	Vec			(const S& size) { init(); resize(size); }
		__forceinline			Vec			(const S& size, const T& val) { init(); resize(size, val); }
		__forceinline			Vec			(const std::initializer_list<T>& src) { init(); copyFrom(src); }
		__forceinline Vec<T>&	operator=	(Vec<T>& rhs) { return *this; }
		__forceinline const T&	operator[]	(const S& index) const { assert(check(index)); return _mem[index]; }
		__forceinline T&		operator[]	(const S& index) { assert(check(index)); return _mem[index]; }
		__forceinline const T&	back		() const { assert(sz); return _mem[sz - 1]; }
		__forceinline T&		back		() { assert(sz); return _mem[sz - 1]; }
		__forceinline			operator T* () { return _mem; }
		__forceinline T*		data		() const { return _mem; }
		__forceinline T*		end			() const { return _mem + sz; }
		__forceinline bool		empty		() const { return !sz; }
		__forceinline S			size		() const { return sz; }
		__forceinline S			capacity	() const { return cap; }
		__forceinline void		pop			() { assert(sz > 0); _mem[--sz].~T(); }
		__forceinline void		insert		(const T& val) { assert(cap > sz);  _mem[sz++] = val; }
		__forceinline void		push		(const T& val) { if (sz == cap) reserve(sz + 1); new (_mem + sz) T(val); sz++; }
		__forceinline void		reserve		(const S& min_cap, const S& size) { reserve(min_cap); sz = size; }
		__forceinline void		lock		() { _m.lock(); }
		__forceinline void		unlock		() { _m.unlock(); }
		__forceinline void		init		() { maxCap = std::numeric_limits<S>::max(), _mem = NULL, sz = 0, cap = 0; }
		__forceinline			Vec			(Vec<T, S>&& orig) { 
			maxCap = std::numeric_limits<S>::max(), _mem = orig._mem, sz = orig.sz, cap = orig.cap; orig.init();
		}
		__forceinline void		init		(const S& off, const S& n, const T& val) {
			if (!val && !off) { std::memset(_mem, 0, n * sizeof(T)); }
			else { for (S i = off; i < n; i++) _mem[i] = val; }
		}
		__forceinline void		resize		(const S& n) {
			if (n == sz) return;
			if (n < sz) shrink(sz - n);
			else expand(n);
		}
		__forceinline void		resize		(const S& n, const T& val) {
			if (n == sz) { init(0, n, val); return; }
			if (n < sz) shrink(sz - n, val);
			else expand(n, val);
		}
		__forceinline void		shrink		(const S& n) {
			assert(n <= sz);
			for (S i = 0; i < n; i++) _mem[--sz].~T();
		}
		__forceinline void		shrink		(const S& n, const T& val) {
			assert(n <= sz);
			for (S i = 0; i < n; i++) _mem[--sz].~T();
			init(0, n, val);
		}
		__forceinline void		expand		(const S& size) {
			if (sz >= size) return;
			reserve(size);
			for (S i = sz; i < size; i++) new (&_mem[i]) T();
			sz = size;
		}
		__forceinline void		expand		(const S& size, const T& val) {
			if (sz >= size) return;
			reserve(size);
			init(sz, size, val);
			sz = size;
		}
		__forceinline void		reserve		(const S& min_cap) {
			if (cap >= min_cap) return;
			if (cap > (maxCap - cap)) cap = min_cap;
			else { cap <<= 1; if (cap < min_cap) cap = min_cap; }
			pfalloc(_mem, sizeof(T) * cap);
		}
		__forceinline void		shrinkCap	() {
			if (!sz) { clear(true); return; }
			pfshrinkAlloc(_mem, sizeof(T) * sz);
			cap = sz;
		}
		template<class Container = Vec<T, S>>
		__forceinline void		copyFrom	(const Container& copy) {
			resize(copy.size());
			std::memcpy(_mem, copy.data(), sz * sizeof(T));
		}
		template<class SS = uint32>
		__forceinline void		copyFrom	(T* copy, const SS& copy_sz) {
			assert(copy_sz <= sz);
			std::memcpy(_mem, copy, sz * sizeof(T));
		}
		__forceinline void		clear		(const bool& _free = false) {
			if (_mem != NULL) {
				for (S i = 0; i < sz; i++) _mem[i].~T();
				sz = 0;
				if (_free) { std::free(_mem); _mem = NULL; cap = 0; }
			}
		}
		__forceinline void		unionize	(const Vec<T, S>& rhs) { unionize(rhs, std::less<T>()); }
		template<class Comparator>
		__forceinline void		unionize	(const Vec<T,S>& rhs, Comparator less) {
			if (empty()) copyFrom(rhs);
			else if (!rhs.empty()) {
				Vec<T, S> lhs = Vec<T, S>(*this);
				expand(lhs.size() + rhs.size());

				S i = 0, j = 0, k = 0;
				while (i < lhs.size() && j < rhs.size()) {
					if (less(lhs[i], rhs[j])) _mem[k++] = lhs[i++];
					else if (less(rhs[j], lhs[i])) _mem[k++] = rhs[j++];
					else { _mem[k++] = lhs[i++]; j++; }
				}
				while (i < lhs.size()) _mem[k++] = lhs[i++];
				while (j < rhs.size()) _mem[k++] = rhs[j++];
				resize(k);
			}
		}
		__forceinline void		intersect	(const Vec<T, S>& rhs) { intersect(rhs, std::less<T>()); }
		template<class Comparator>
		__forceinline void		intersect	(const Vec<T, S>& rhs, Comparator less) {
			if (empty() || rhs.empty()) clear(true);
			else {
				if (size() < rhs.size()) expand(rhs.size());

				S i = 0, j = 0, k = 0;
				while (i < size() && j < rhs.size()) {
					if (less(_mem[i], rhs[j])) i++;
					else if (less(rhs[j], _mem[i])) j++;
					else { _mem[k++] = _mem[i++]; j++; }
				}
				resize(k);
			}
		}
	};
	// vector types
	typedef Vec<int> Vec1D;
	typedef Vec<uint32> uVec1D;
	typedef Vec<uint32, int> Lits_t;
}

#endif

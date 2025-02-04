/***********************************************************************[pfralloc.h]
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

#ifndef __RALLOC_
#define __RALLOC_

#include "pfdtypes.h"
#include <cstdlib>
#include <cstring>

namespace pFROST {

	class MEMOUTEXCEPTION {};

	template <class T>
	void pfalloc(T*& mem, size_t bytes) {
		T* _mem = (T*)std::realloc(mem, bytes);
		if (_mem == NULL) throw MEMOUTEXCEPTION();
		mem = _mem;
	}

	template <class T>
	void pfshrinkAlloc(T*& mem, size_t bytes) {
		T* _mem = NULL;
		_mem = (T*)std::realloc(_mem, bytes);
		if (_mem == NULL) throw MEMOUTEXCEPTION();
		std::memcpy(_mem, mem, bytes);
		std::free(mem);
		mem = _mem;
	}

}

#endif
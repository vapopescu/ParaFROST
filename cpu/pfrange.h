/***********************************************************************[pfalloc.h]
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

#pragma once
#include "pfvec.h"

namespace pFROST {
	template<class T>
	class Range : public Vec<T> {
	private:
		void init(T begin, T end, T step) {
			this->reserve((end - begin) / step);
			for (T i = begin; i < end; i += step) this->push(i);
		}

	public:
		Range<T>()							: Vec<T>()		{ init(0, 0, 1);  }
		Range<T>(T end)						: Vec<T>()		{ init(0, end, 1); }
		Range<T>(T begin, T end)			: Vec<T>()		{ init(begin, end, 1); }
		Range<T>(T begin, T end, T step)	: Vec<T>()		{ init(begin, end, step); }
	};
}
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
#include <vector>

namespace pFROST {
	template<class T>
	class Range : public std::vector<T> {
	private:
		void init(T begin, T end, T step) {
			for (T i = begin; i < end; i += step) {
				this->push_back(i);
			}
		}

	public:
		Range<T>()							: std::vector<T>() { init(0, 0, 1);  }
		Range<T>(T end)						: std::vector<T>() { init(0, end, 1); }
		Range<T>(T begin, T end)			: std::vector<T>() { init(begin, end, 1); }
		Range<T>(T begin, T end, T step)	: std::vector<T>() { init(begin, end, step); }
	};
}
/***********************************************************************[pfsimp.h]
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

#include <list>
#include <set>
#include <algorithm>

namespace pFROST {
	template<class T = uint32>
	class Path {
	protected:
		std::list<T> _trace;
		std::set<T> _itemSet;
	public:
		Path() : _trace(), _itemSet() {}
		~Path() {}
		Path(std::initializer_list<T> init) : _trace(init), _itemSet(init) {}
		Path(const Path& src) : _trace(src._trace), _itemSet(src._itemSet) {}

		inline void								push		(const T& item) { _trace.push_back(item); _itemSet.insert(item); }
		inline const T&							back		() const { return _trace.back(); }
		inline void								pop			() { _itemSet.erase(_trace.back()); _trace.pop_back(); }
		inline size_t							size		() const { return _trace.size(); }
		inline const std::set<T>&				itemSet		() const { return _itemSet; }
	};

	typedef std::pair<uint32, Path<uint32>> NodePath;
}

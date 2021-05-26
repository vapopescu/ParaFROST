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

#include "pfvec.h"
#include <shared_mutex>

namespace pFROST {
	typedef std::pair<uint32, S_REF> Edge;
	typedef unsigned char NodeState;

	static const NodeState _VISITED_ = 0x01;
	static const NodeState _EXPLORED_ = 0x02;
	static const NodeState _REDUCED_ = 0x04;

	class Node {
	protected:
		Vec<Edge>					_out, _in;
		uVec1D						_desc;
		NodeState					_st;
		mutable std::shared_mutex	_m;

		inline void		appendEdge		(Vec<Edge>& vec, const uint32& lit, const S_REF& c) { vec.push(Edge(lit, c)); }
		inline void		insertEdge		(Vec<Edge>& vec, const uint32& lit, const S_REF& c)
		{
			uint32 i = vec.size();
			vec.push(Edge());

			while (vec[i - 1].first > lit && i > 0) {
				vec[i] = vec[i - 1];
				i--;
			}

			vec[i] = Edge(lit, c);
		}
		inline void		deleteEdge		(Vec<Edge>& vec, const uint32& lit)
		{
			uint32 n = 0;
			for (uint32 i = 0; i < vec.size(); i++) {
				if (vec[i].first != lit) vec[n++] = vec[i];
			}
			vec.resize(n);
		}
		inline bool		empty			(const Vec<Edge>& vec) const
		{
			bool retVal = true;
			if (!vec.empty()) {
				for (uint32 i = 0; i < vec.size(); i++) {
					if (!vec[i].second->deleted()) {
						retVal = false;
						break;
					}
				}
			}
			return retVal;
		}
	public:
		inline void					clear			() { _st = 0; _out.clear(true); _in.clear(true); _desc.clear(true); }
		inline void					lockRead		() const { _m.lock_shared(); }
		inline void					unlockRead		() const { _m.unlock_shared(); }
		inline void					lock			() const { _m.lock(); }
		inline void					unlock			() const { _m.unlock(); }
		inline void					appendChild		(const uint32& lit, const S_REF& c) { appendEdge(_out, lit, c); }
		inline void					insertChild		(const uint32& lit, const S_REF& c) { insertEdge(_out, lit, c); }
		inline void					deleteChild		(const uint32& lit) { deleteEdge(_out, lit); }
		inline void					appendParent	(const uint32& lit, const S_REF& c) { appendEdge(_in, lit, c); }
		inline void					insertParent	(const uint32& lit, const S_REF& c) { insertEdge(_in, lit, c); }
		inline void					deleteParent	(const uint32& lit) { deleteEdge(_in, lit); }
		inline bool					isDeadEnd		() const { return empty(_out); }
		inline bool					isOrphan		() const { return empty(_in); }
		inline bool					isVisited		() const { return _st & _VISITED_; }
		inline bool					isExplored		() const { return _st & _EXPLORED_; }
		inline bool					isReduced		() const { return _st & _REDUCED_; }
		inline void					markVisited		() { _st |= _VISITED_; }
		inline void					markExplored	() { _st |= _EXPLORED_; }
		inline void					markReduced		() { _st |= _REDUCED_; }
		inline Vec<Edge>&			children		() { return _out; }
		inline const Vec<Edge>&		children		() const { return _out; }
		inline Vec<Edge>&			parents			() { return _in; }
		inline const Vec<Edge>&		parents			() const { return _in; }
		inline uVec1D&				descendants		() { return _desc; }
		inline const uVec1D&		descendants		() const { return _desc; }
		inline void					sortEdges		() {
			std::sort(_out.data(), _out.data() + _out.size());
			std::sort(_in.data(), _in.data() + _in.size());
		}
	};
}

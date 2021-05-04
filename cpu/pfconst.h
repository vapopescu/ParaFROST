/***********************************************************************[pfconst.h]
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

#ifndef __GL_MACROS_
#define __GL_MACROS_

#include "pfdtypes.h"

extern bool quiet_en;
extern int verbose;
extern bool color;

namespace pFROST {
//=======================================//
//      ParaFROST Parameters & Macros    //
//=======================================//
#define MBYTE 0x00100000
#define KBYTE 0x00000400
#define GBYTE 0x40000000
#define NOREF UINT64_MAX
#define NOVAR UINT32_MAX
#define INIT_CAP 32
#define UNSOLVED -1
#define UNSAT 0
#define SAT 1
#define ORGPHASE 1
#define INVPHASE 2
#define FLIPPHASE 3
#define BESTPHASE 4
#define RANDPHASE 5
#define AWAKEN_SUCC	0
#define AWAKEN_FAIL 1
#define SALLOC_FAIL 2
//======== DANGER ZONE =========
#define NEG_SIGN	0x00000001
#define HASH_MASK	0x0000001F
#define NOVAL_MASK	(LIT_ST)-2
#define UNDEFINED	(LIT_ST)-1
#define VAL_MASK	(LIT_ST) 1
#define ACTIVE		(LIT_ST) 0
#define MELTED		(LIT_ST) 1
#define FROZEN		(LIT_ST) 2
#define ANALYZED_M	(LIT_ST) 0x01
#define REMOVABLE_M	(LIT_ST) 0x02
#define POISONED_M	(LIT_ST) 0x04
#define KEEP_M		(LIT_ST) 0x08
#define USAGE_MAX	(CL_ST)0x03
#define USAGE_RES	(CL_ST)0x03
#define USAGE_OFF	(CL_ST)0x02
#define CMOLTEN		(CL_ST)0x01
#define CADDED		(CL_ST)0x02
#define RMOLTEN		(CL_ST)0xFE
#define USAGET3		(CL_ST)0x01
#define USAGET2		(CL_ST)0x02
#define ORIGINAL	(CL_ST)0x01
#define LEARNT		(CL_ST)0x02
#define DELETED		(CL_ST)0x04
#define ISORG(x)		((x) & ORIGINAL)
#define POS(x)			((x) & 0xFFFFFFFE)
#define ABS(x)			((x) >> 1)
#define V2L(x)			((x) << 1)
#define SIGN(x)			((x) & NEG_SIGN)
#define NEG(x)			((x) | NEG_SIGN)
#define V2DEC(x,s)		(V2L(x) | (s))
#define FLIP(x)			((x) ^ NEG_SIGN)
#define HASH(x)			((x) & HASH_MASK)
#define MAPHASH(x)		(1UL << HASH(x))
#define	REMOVABLE(x)	((x) & REMOVABLE_M)	
#define	POISONED(x)		((x) & POISONED_M)
#define	KEPT(x)			((x) & KEEP_M)
#define UNASSIGNED(x)	((x) & NOVAL_MASK)
#define REASON(x)		((x) ^ NOREF)
#define DECISION(x)		(!REASON(x))
//==============================

}

#endif
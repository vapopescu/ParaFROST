/***********************************************************************[pfcolor.h]
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

#ifndef __COLOR_
#define __COLOR_

#include <cstdio>

#define CNORMAL     (color ? "\x1B[0m" : "")
#define CUNDERLINE	(color ? "\x1B[4m" : "")
#define CRED        (color ? "\x1B[31m" : "")
#define CGREEN      (color ? "\x1B[32m" : "")
#define CYELLOW     (color ? "\x1B[33m" : "")
#define CBLUE       (color ? "\x1B[34m" : "")
#define CMAGENTA    (color ? "\x1B[35m" : "")
#define CCYAN       (color ? "\x1B[36m" : "")
#define CWHITE      (color ? "\x1B[37m" : "")
#define CLRED       (color ? "\x1B[91m" : "")
#define CLGREEN     (color ? "\x1B[92m" : "")
#define CLYELLOW    (color ? "\x1B[93m" : "")
#define CLBLUE      (color ? "\x1B[94m" : "")
#define CLMAGENTA   (color ? "\x1B[95m" : "")
#define CLCYAN      (color ? "\x1B[96m" : "")
#define CGREEN0		(color ? "\x1B[38;5;78m" : "")
#define CGREEN1		(color ? "\x1B[38;5;77m" : "")
#define CGREEN2		(color ? "\x1B[38;5;76m" : "")
#define CGREEN3		(color ? "\x1B[38;5;40m" : "")
#define CORANGE0	(color ? "\x1B[38;5;203m" : "")
#define CORANGE1	(color ? "\x1B[38;5;202m" : "")
#define CVIOLET0	(color ? "\x1B[38;5;168m" : "")
#define CVIOLET1	(color ? "\x1B[38;5;170m" : "")
#define CVIOLET2	(color ? "\x1B[38;5;165m" : "")
#define CVIOLET3	(color ? "\x1B[38;5;164m" : "")
#define CVIOLET4	(color ? "\x1B[38;5;163m" : "")
#define CVIOLET5	(color ? "\x1B[38;5;125m" : "")

#define CSOLVER		(color ? "\x1B[38;5;117m" : "")
#define CAUTHOR		(color ? "\x1B[38;5;116m" : "")
#define CRIGHTS		(color ? "\x1B[38;5;1m" : "")
#define CERROR		(color ? "\x1B[38;5;1m" : "")
#define CWARNING	(color ? "\x1B[38;5;226m" : "")
#define CHEADER		(color ? "\x1B[38;5;109m" : "")
#define CREPORT		(color ? "\x1B[38;5;187m" : "")
#define CREPORTVAL	(color ? "\x1B[38;5;106m" : "")
#define CLOGGING	(color ? "\x1B[38;5;225m" : "")
#define CCONFLICT	(color ? "\x1B[38;5;198m" : "")
#define CHELP		(color ? "\x1B[38;5;108m" : "")
#define CARGDEFAULT	(color ? "\x1B[38;5;187m" : "")
#define CARGVALUE	(color ? "\x1B[38;5;34m" : "")
#define CARGON		(color ? "\x1B[38;5;34m" : "")
#define CARGOFF		(color ? "\x1B[38;5;124m" : "")

#define SETCOLOR(COLOR, STD) if (color) fprintf(STD, "%s", COLOR);

#endif
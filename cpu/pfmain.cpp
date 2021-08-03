/***********************************************************************[pfmain.cpp]
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

#include "pfsolve.h"

using namespace pFROST;

bool quiet_en = false;
int verbose = -1;
bool color = false;

int main(int argc, char **argv)
{
	BOOL_OPT opt_quiet_en("q", "enable quiet mode, same as verbose=0", false);
	INT_OPT opt_verbose("verbose", "set the verbosity", 1, INT32R(0, 4));
	BOOL_OPT opt_color_en("color", "enable colorful output in the console", false);
	INT_OPT opt_timeout("timeout", "set the timeout in seconds", 0, INT32R(0, INT32_MAX));
	if (argc == 1) PFLOGE("no input file specified");
	try {
		parseArguments(argc, argv);
		quiet_en = opt_quiet_en; 
		verbose = opt_verbose;
		color = opt_color_en;
		if (quiet_en) verbose = 0;
		else if (!verbose) quiet_en = true;
		if (!quiet_en && verbose) {
			PFNAME("ParaFROST (Parallel Formal Reasoning Of Satisfiability)");
			PFAUTHORS("Muhammad Osama and Anton Wijs");
			PFRIGHTS("Technische Universiteit Eindhoven (TU/e)");
			PFLRULER('-', RULELEN);
			PFLOGN0(" Embedded options: ");
			for (int i = 0, j = 0; i < options.size(); i++) {
				if (options[i]->isParsed()) {
					options[i]->printArgument();
					if (++j % 4 == 0) { putc('\n', stdout); PFLOGN0("\t\t"); }
				}
			}
			putc('\n', stdout); PFLRULER('-', RULELEN);
		}
		string formula = argv[1];
		if (formula.find(".cnf") == -1 && formula.find(".dimacs") == -1) PFLOGE("input file not recognizable");
		signal_handler(handler_terminate);
		ParaFROST* pFrost = new ParaFROST(formula);
		pfrost = pFrost;
		signal_handler(handler_mercy_interrupt, handler_mercy_timeout);
		pFrost->solve();
		if (!quiet_en) PFLOG0("");
		PFLOGN2(1, " Cleaning up..");
		pfrost = NULL;
		delete pFrost;
		PFLDONE(1, 5);
		if (!quiet_en) PFLRULER('-', RULELEN);
		return 0;
	}
	catch (MEMOUTEXCEPTION&) {
		PFLOGEN("Memoryout");
		PFLOGS("UNKNOWN");
		return 0;
	}
}
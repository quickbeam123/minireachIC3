/********************************************************************************************
Copyright (c) 2013, Martin Suda
Max-Planck-Institut für Informatik, Saarbrücken, Germany
 
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Aiger_2_Spec_h
#define Aiger_2_Spec_h

#include "mtl/Vec.h"
#include "core/SolverTypes.h"

typedef Minisat::vec< Minisat::vec<Minisat::Lit> > Clauses;

void aiger_LoadSpec( /* input:*/ 
                        const char* input_name, // can be 0 for parsing stdin
                        int reversed,
                        int pg,
                        int verbose,
                        int kth_property,       // can be -1 to expect exactly one property and return it
                        int parse_liveness,     // looks for liveness property instead of bad state
                     /*output:*/ int &signature_size, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step);

#endif
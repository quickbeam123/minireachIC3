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

#ifndef DisjMarkingSolver_h
#define DisjMarkingSolver_h

#include <map>

#include "core/Aiger2Spec.h"
#include "core/Solver.h"
#include "core/MarkingSolver.h"

namespace Minisat {

class DisjunctionMaintainingMarkingSolver : public MarkingSolver {
  public:
    // like with MarkingSolver, but the next available slot is reserved for the disjuction literal, which is returned
    Lit initilazeSignature(int number_of_basic_vars);
  
    // initially, the disjuction literal returned by the function above implies FALSE
  
    // disjunction literal is weakened to imply all it implied before OR the conjunction of the given units
    void disjoinWithUnits(const vec<Lit>& units);
  
    // disjunction literal is weakened to imply all it implied before OR the given cnf
    void disjoinWithCNF(const Clauses& cnf);
  
    void preprocessAssumptions(const vec<Lit>& clause_assumps, const vec<int>& marker_assumps);
  
  protected:
    Var disj_var;
    vec<Var> connectors;
  
    void ensureEnoughConnectors();
};

}

#endif
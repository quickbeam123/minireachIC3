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

#include "core/DisjMarkingSolver.h"
#include "utils/Options.h"
#include "mtl/Sort.h"

using namespace Minisat;

Lit DisjunctionMaintainingMarkingSolver::initilazeSignature(int number_of_basic_vars) {
  for (int i = 0; i < number_of_basic_vars; i++)
    newVar();
  
  disj_var = newVar();
  
  connectors.push(disj_var);
  
  base_marker_index = nVars();
  
  return mkLit(disj_var);
}

static const int CONN_CL_LEN = 8; // must be at least 2

void DisjunctionMaintainingMarkingSolver::ensureEnoughConnectors() {
  if (connectors.size() == 1) {
    add_tmp.clear();
    add_tmp.push(mkLit(connectors[0],true));
    connectors.clear();
    for (int i = 0; i < CONN_CL_LEN; i++) {
      Var v = newVar();
      connectors.push(v);
      add_tmp.push(mkLit(v));
    }
    
    addClause_(add_tmp);
  }
}

void DisjunctionMaintainingMarkingSolver::disjoinWithUnits(const vec<Lit>& units) {
  ensureEnoughConnectors();
  
  // define the added disjunct
  add_tmp.clear();
  add_tmp.push(mkLit(connectors.last(),true));
  connectors.pop();
  add_tmp.push();
  
  for (int i = 0; i < units.size(); i++) {
    add_tmp[1] = units[i];
    addClause_(add_tmp);
  }
}

void DisjunctionMaintainingMarkingSolver::disjoinWithCNF(const Clauses& cnf) {
  ensureEnoughConnectors();
  
  Lit guard = mkLit(connectors.last(),true);
  connectors.pop();
  for (int i = 0; i < cnf.size(); i++) {
    const vec<Lit> & cl = cnf[i];
    cl.copyTo(add_tmp);
    add_tmp.push(guard);
    addClause_(add_tmp);
  }
}

void DisjunctionMaintainingMarkingSolver::preprocessAssumptions(const vec<Lit>& clause_assumps, const vec<int>& marker_assumps) {
  MarkingSolver::preprocessAssumptions(clause_assumps,marker_assumps);
  for (int i = 0; i < connectors.size(); i++)
    assumptions.push(mkLit(connectors[i],true));
}


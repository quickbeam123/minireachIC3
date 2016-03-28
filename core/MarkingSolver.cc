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

#include "core/MarkingSolver.h"
#include "utils/Options.h"
#include "mtl/Sort.h"

using namespace Minisat;

MarkingSolver::MarkingSolver() : base_marker_index(0) {}

void MarkingSolver::initilazeSignature(int number_of_basic_vars) {
  for (int i = 0; i < number_of_basic_vars; i++ )
    newVar();
    
  base_marker_index = nVars();
}

Var MarkingSolver::ensureMarkerRegistered(int id) {
  std::map<int,Var>::const_iterator it = id2var.find(id);
  if (it != id2var.end()) //already registered
    return it->second;

  Var v = newVar();
  id2var[id] = v;
  var2id[v] = id;
  return v;
}

void MarkingSolver::invalidateMarker(int id) {
  if (id2var.find(id) == id2var.end()) // not valid anyway
    return;
  
  Var v = id2var[id];  
  releaseVar(mkLit(v));
         
  int removed;
  removed = id2var.erase(id);
  assert(removed == 1);    
  removed = var2id.erase(v);
  assert(removed == 1);
}

void MarkingSolver::invalidateAll() {
  while (id2var.size() > 0)
    invalidateMarker(id2var.begin()->first);
}

bool MarkingSolver::addClause(const vec<Lit>& ps, const vec<int>& markers) {
  ps.copyTo(add_tmp);
  for (int i = 0; i < markers.size(); i++) {
    ensureMarkerRegistered(markers[i]);      
    add_tmp.push(mkLit(id2var[markers[i]]));
  }  
  return addClause_(add_tmp);
}

void MarkingSolver::preprocessAssumptions(const vec<Lit>& clause_assumps, const vec<int>& marker_assumps) {
  clause_assumps.copyTo(assumptions);
  
  for (int i = 0; i < marker_assumps.size(); i++) {
    int id = marker_assumps[i];
    ensureMarkerRegistered(id);    
    assumptions.push(mkLit(id2var[id],true));
  }
}

void MarkingSolver::preprocessConflict(vec<Lit>& out_conflict, vec<int>& out_markers) {
  out_conflict.clear();
  out_markers.clear();
  
  for (int i = 0; i < conflict.size(); i++) {
    Lit l = conflict[i];
    Var v = var(l);
    if (v < base_marker_index)
      out_conflict.push(l);
    else {
      std::map<Var,int>::iterator it = var2id.find(v);
      if (it != var2id.end()) { // because it can also be one of the connectors (see DisjunctionMaintainingMarkingSolver)
        assert(!sign(l));
        out_markers.push(var2id[v]);
      }
    }         
  }
}
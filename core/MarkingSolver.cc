#include "core/MarkingSolver.h"
#include "utils/Options.h"
#include "mtl/Sort.h"

using namespace Minisat;

MarkingSolver::MarkingSolver() : base_marker_index(0) {}
MarkingSolver::~MarkingSolver() {}

void MarkingSolver::initilazeSignature(int number_of_basic_vars) {
  for (int i = 0; i < number_of_basic_vars; i++ )
    newVar();
    
  base_marker_index = nVars();
}

void MarkingSolver::ensureMarkerRegistered(int id) {
  if (id2var.find(id) != id2var.end()) //already registered
    return;

  Var v = newVar();
  id2var[id] = v;
  var2id[v] = id;
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
      assert(!sign(l));      
      out_markers.push(var2id[v]);
    }         
  }
}
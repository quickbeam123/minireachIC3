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

#ifndef MarkingSolver_h
#define MarkingSolver_h

#include <map>

#include "core/Solver.h"

namespace Minisat {

class MarkingSolver : public Solver {
  public:
    MarkingSolver();
    ~MarkingSolver();
  
    void initilazeSignature(int number_of_basic_vars);              // the solver may allocate additional variables to serve as markers; so after this called, newVar shouldn't be called anymore   
    bool addClause (const vec<Lit>& ps, const vec<int>& markers);   // Add a clause to the solver, enriched with a set of markers (markers must be registered beforehand);
    
    void preprocessAssumptions(const vec<Lit>& clause_assumps, const vec<int>& marker_assumps); // combines the supplied clause_assumps with translated marker_assumps
    bool solve() { budgetOff(); return (solve_() == l_True); }  //triggers the actual solving
    void preprocessConflict(vec<Lit>& conflict, vec<int>& markers);  // splits the derived conflict clause into the "core clause" over user supplied assumption and the markers
         
    Lit getAssump(int i) { assert(i < assumptions.size()); return assumptions[i]; }
    void setAssump(int i, Lit l) { assert(i < assumptions.size()); assumptions[i] = l; }
        
    void invalidateMarker(int id);    // all clauses with the given marker are removed from the solver 
                                      // (remove doesn't necessarily mean deleted, they can be implicitly removed by assuming the respective marker variable is true;
                                      // the solver may later decide to really delete such clauses, and to recycle the respective variable for a newly requested marker)
                                      // (can be called even on previously unregistered marker, in which case this is no-op)
    void invalidateAll();
    
  protected:    
    int base_marker_index;
  
    void ensureMarkerRegistered(int id);    
    std::map<int,Var> id2var;  // map ids->vars, stores the variable currently assigned to a marker with the given id    
    std::map<Var,int> var2id;  // for storing the inverse map
};

}

#endif
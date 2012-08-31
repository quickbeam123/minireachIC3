/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"
#include "mtl/Sort.h"

#include "simp/SimpSolver.h"

#include "core/Aiger2Spec.h"

#include <set>
#include <map>
#include <algorithm>
#include <queue>

using namespace Minisat;

static BoolOption opt_verbose     ("PARSE", "v", "Verbose output.", true);
static BoolOption opt_pphase     ("MAIN", "pphase", "Print phase.", false);

static BoolOption opt_pg          ("PARSE", "pg","Plaisted-Greenbaum CNF encoding.", true);
static IntOption  opt_kth_property("PARSE", "id","Pick a particular property from Multi-Property input (indexing from 0).\n"
                                                 "-1 picks the only one and aborts if there is no such.\n"
                                                 "-2 just prints the ids of all available and aborts", -1, IntRange(-2, INT32_MAX));

static BoolOption opt_reversed    ("PARSE", "rev", "Swap initial and goal formulas after parsing.", false);
static BoolOption opt_elimination ("MAIN", "simp", "Perform variable elimination before actual solving.", true);

static IntOption opt_monot ("MAIN", "mon", "Make the specificiation monotone (1 - backward, 2 - forward, 3 - both).", 1, IntRange(0,3));
static IntOption opt_minimize ("MAIN", "min", "Minimize learned clauses.", 1, IntRange(0,3));

static BoolOption opt_dot     ("MAIN", "dot", "Generate dot output. Then use: dot -Knop -Tps2 out.dot -o out.ps", false);
static IntOption opt_phaselim ("MAIN", "phaselim", "Terminate after a given number of phases.", 0, IntRange(0,INT32_MAX));

static BoolOption opt_subsume ("MAIN", "subsume", "Reduce layers by subsumption.", true);

//=================================================================================================

static const int NODEXDIST = 80;
static const int NODEYDIST = 80;

void printClause(const vec<Lit> &clause) {
  for (int i = 0; i < clause.size(); i++)
    printf("%s%d ",sign(clause[i])?"-":"",var(clause[i]));
    
  printf("\n");
}

void print(std::ostream &stream, int i) {
  stream << i;
}

void print(std::ostream &stream, Lit l) {  
  stream << (sign(l)?"-":"") << var(l);
}

void printClauseData(vec<int>& data, int layer_idx) {
  printf("C?@%d || ",layer_idx);
  for (int i = 0; i < data.size(); i++) {
    printf(" %d",data[i]);   
  }
  printf("\n");
}

template <typename S>
void initializeSolver(S &solver, int i, int sigsize) {
  // 0,1,...,sigsize-1           the basic signature
  // sigsize,...,2*sigsize-1     the primed signature
  // 2*sigsize                   the initial marker 
  // 2*sigsize+1                 the goal marker 
   
  for (int j = 0; j < 2*sigsize+2; j++) {
    solver.newVar();
  }
  //printf("Initialized solver[%d]\n",i);   
}

static int ids = 0;

struct Obligation {
  int id;
  int idx;
  int depth;
  vec<Lit> ma;
  
  Obligation *next; // used for the list of free obligations
  
  Obligation(int given) {
    id = given;
  }
  
  void print() {
    printf("id: %d, idx: %d, depth: %d, size: %d\n",id,idx,depth,ma.size());
  }
  
};

struct ObligationCmp {
  bool operator() (Obligation *lhs, Obligation *rhs) const
  {   
    if (lhs->idx > rhs->idx) // I am small (less likely to be picked next) if my index is high
      return true;      
      
    if (lhs->idx < rhs->idx)
      return false;      
          
    return (lhs->depth < rhs->depth);   // In case of a draw on above, the deeper the better
  }
};

typedef std::map< vec<Lit>, int> ClauseIds;

bool subsumes(const vec<Lit> &c1, const vec<Lit> &c2) { // assumed sorted
  vec<int> dummy;
   
  if (c1.size() > c2.size())
    return false;

  int j = 0;
  for (int i = 0; i < c1.size(); i++) {    
    while (j < c2.size() && c2[j] < c1[i])
      j++;
    if (j == c2.size())
      return false;
    if (c1[i] != c2[j])
      return false;
    j++;
  }

  return true;
}

struct SolvingContext {
  int sigsize;

  vec< Solver* > solvers;
  vec< Clauses* > layers;
    
  int in_layers;
  int in_layers_sz;
  ClauseIds clause_ids;  
  
  int phase;
  int called;
  int propagated_starstar;  
    
  int min_layer;
  int max_depth;
  
  Obligation *pool;
  int poolsize;  
     
  Obligation* acquireObligation() {
    if (pool) {
      Obligation* res = pool;
      res->id = ids++;
      pool = pool->next;      
      return res;
    } else {
      poolsize++;
      return new Obligation(ids++);
    }
  }
  
  void releaseObligation(Obligation* ob) {
    ob->next = pool;
    pool = ob;
  }
  
  std::priority_queue<Obligation*,std::vector<Obligation*>,ObligationCmp> obligations;
   
  SolvingContext() : in_layers(0), in_layers_sz(0), propagated_starstar(0), pool(0), poolsize(0)  { }
  
  ~SolvingContext() {
    if (opt_verbose)
      printStat();
        
    for (int i = 0; i < solvers.size(); i++)
      delete solvers[i];
      
    for (int i = 0; i < layers.size(); i++)
      delete layers[i];
          
    while (pool) {
      Obligation* next = pool->next;
      delete pool;
      pool = next;
    }
  }
  
  int conflicts() {
    int result = 0;
    for (int i = 0; i < solvers.size(); i++)
      result += (int)solvers[i]->conflicts;
    return result;      
  }
  
  void printStat() {
    if (opt_dot) {
      printf("graph [bb=\"0,0,%zu,%d\"];\n",NODEXDIST*(clause_ids.size()+1),NODEYDIST*(layers.size()+1));
      printf("}\n");    
    }
    
    printf("// Game over during phase: %d, solver called %d times, propagated_starstar %d clauses.\n",phase,called,propagated_starstar);
    printf("// In layers %d (%d unique) => %f ratio.\n",in_layers,(int)clause_ids.size(),(1.0*clause_ids.size())/in_layers);
    printf("// Average clause len: %f\n",1.0*in_layers_sz/in_layers);
  }
  
  vec<Lit> temp_ma;
  
  void minimizeConflict(Solver& solver, vec<Lit>& ma) {
    if (opt_minimize == 1) {  // minimizing conflict clause -- the light version        
      ma.copyTo(temp_ma);
      
      int last_size = sigsize;
      int mincall = 0;             
  
      while (last_size > solver.conflict.size()) {
        temp_ma.shrink(last_size);
        last_size = solver.conflict.size();
        mincall++;
      
        for (int i = 0; i < solver.conflict.size(); i ++)
          temp_ma.push(mkLit(var(solver.conflict[i]),!sign(solver.conflict[i])));
      
        bool res = solver.solve(temp_ma);
        assert(!res); // carefull, the call to solve() itself cannot be removed!
      }       
    } else if (opt_minimize > 1) {  // minimizing conflict clause -- the do as much as possible version
      ma.copyTo(temp_ma);
    
      if (opt_minimize > 2)
        sort(solver.conflict,LessThan_default<Lit>());
      else
        sort(solver.conflict,GreaterThan_default<Lit>());           
      
      temp_ma.clear();
      for (int i = 0; i < solver.conflict.size(); i ++)
        temp_ma.push(mkLit(var(solver.conflict[i]),!sign(solver.conflict[i])));

      Lit extra = lit_Undef;      
      // first phase - dropping the last guy
      while (temp_ma.size() > 0) {
        extra = temp_ma.last();
        temp_ma.pop();
        
        if (solver.solve(temp_ma))
          break;
        else
          extra = lit_Undef; // forget him
      }

      // second phase - dropping someone in the middle
      if (extra != lit_Undef) {
        for (int i = temp_ma.size()-1; i >= 0; i--) {
          Lit dropped = temp_ma[i];
          temp_ma[i] = extra;
      
          if (solver.solve(temp_ma))  //undo
            temp_ma[i] = dropped;
          else { // keep him out
            extra = temp_ma.last();
            temp_ma.pop();
          }
        }
        
        temp_ma.push(extra);
      }
      
      // reconstruct the conflict clause from MA (note that the last call could have ended up SAT)
      solver.conflict.clear();
      for (int i = 0; i < temp_ma.size(); i++)
        solver.conflict.push(mkLit(var(temp_ma[i]),!sign(temp_ma[i])));                        
    }
  }  
  
  void pruneLayers(vec<Lit>& clause, int from, int to) { // remove subsumed clauses   
    for (int i = from; i <= to; i++) {
      Clauses &layer = *layers[i];
      for (int j = 0; j < layer.size();)
        if (subsumes(clause,layer[j])) {
          if (j < layer.size()-1)
            layer.last().moveTo(layer[j]);
            
          layer.pop();
        } else
          j++;
    }
  }
  
  bool processObligations() {
    vec<Lit> learnt;
  
    while (!obligations.empty()) {
      Obligation *ob = obligations.top(); obligations.pop();
      
      //printf("Picked%2zu| ",obligations.size()+1); ob->print();
    
      int layer_idx = ob->idx;
      vec<Lit> &our_ma = ob->ma;          
      Solver &our_solver = *solvers[layer_idx];      
    
      if (layer_idx < min_layer)
        min_layer = layer_idx;
    
      if (ob->depth > max_depth)
        max_depth = ob->depth;
    
      // experiment -- does this (potentially rescheduled) obligation have a chance to improve the current layers at all?
      /*
      if (layer_idx < phase) {
        vec<Lit> temp_ma;
        for (int i = 0; i < our_ma.size(); i++)
          if (var(our_ma[i])<sigsize)
            temp_ma.push(mkLit(var(our_ma[i])+sigsize,sign(our_ma[i])));
          else
            temp_ma.push(our_ma[i]);
          
        Solver&solver =*solvers[layer_idx+1];
        
        if (solver.solve(temp_ma))
          printf("+");
        else 
          printf("-");
      }
      */
    
      if (called++,our_solver.simplify(),our_solver.solve(our_ma)) {
      
        if (layer_idx == 0) {
          printf("// SAT: model of length %d found\n",ob->depth+1);
          return true;
        }

        // going forward
        Obligation *new_ob = acquireObligation();
        new_ob->idx = layer_idx-1;
        new_ob->depth = ob->depth+1;
  
        vec<Lit>& ma = new_ob->ma;
        ma.clear();
        ma.push(mkLit(2*sigsize, false)); // L_initial - not needed if we add the unit right at the end of iterativeSearch's iteration (see the heuristic there)
        ma.push(mkLit(2*sigsize+1,true)); // not (L_goal)
      
        for (int j = 0; j < sigsize; j++) {
          assert(our_solver.model[j+sigsize] != l_Undef);      
          ma.push(mkLit(j,our_solver.model[j+sigsize] == l_False));
        }
        
        //printf("Old kept| "); ob->print();
        obligations.push(ob);
        //printf("New goes| "); new_ob->print();      
        obligations.push(new_ob);
      } else if (layer_idx < phase) {   //chance to update layers
        Clauses &layer = *layers[layer_idx+1];
        
        minimizeConflict(our_solver,our_ma);
          
        bool fromGoal = false;
        vec<Lit> &conflict = our_solver.conflict;    
                  
        learnt.clear();
        for (int j = 0; j < conflict.size(); j++) {              
          if (var(conflict[j]) == 2*sigsize+1) {
            assert(!sign(conflict[j]));
            fromGoal = true;
          } else if (var(conflict[j]) == 2*sigsize) {
            assert(sign(conflict[j]));
            // the step clause marker doesn't go into learned clauses
          } else {
            assert(var(conflict[j])<sigsize);
            learnt.push(mkLit(var(conflict[j])+sigsize,sign(conflict[j])));
          }
        }
      
        if (fromGoal) {
          learnt.push(mkLit(2*sigsize+1));
          
          sort(learnt);
          if (opt_subsume) 
            pruneLayers(learnt,1,layer_idx+1);                            
          layer.push(learnt);
          in_layers++;
          in_layers_sz += learnt.size();

          int id;
          if (clause_ids.find(learnt) == clause_ids.end()) {
            id = clause_ids.size()+1;
            clause_ids[learnt] = id;
          } else {
            id = clause_ids[learnt];
          }         
          
          if (opt_dot) {
            printf("\"%d_%d\" [label=%d,style=filled,colorscheme=\"%s\", color=\"%d\", pos=\"%d,%d\", width=\"0.75\", height=\"0.51389\"];\n",
                  id,layer_idx,in_layers,phase & 1 ? "blues9" : "oranges9" , (((phase-1) >> 1) % 9)+1,    NODEXDIST*id,NODEYDIST*(layer_idx+1));
          }
          
          for (int i = 1; i <= layer_idx+1; i++) {
            Solver&solver = *solvers[i];
            solver.addClause(learnt);         
          }                    
        } else {
          Solver& solver =  *solvers[layer_idx+1];
          propagated_starstar++;
          solver.addClause(learnt);         
        
          // possibly important heuristic could come here: 
          // remembering and carrying elsewhere (towards solvers.begin -- mind the span -- is always safe) learned (*,*)-clauses          
          // however, for aiger, where the relation is a priori "total", this branch never executes
        }   
      
        ob->idx++;
        //printf("Resched | "); ob->print();
        obligations.push(ob);                      
      } else {        
        if (ob->depth == 0) { //"base level conflict"
          vec<Lit>& conflict = our_solver.conflict;

          assert(conflict.size() <= 2);
                       
          if (conflict.size() < 2) {
            printf("// UNSAT: unconditional empty clause derived, ");        
            if (conflict.size() == 0)
              printf("in fact a (*,*)-clause.\n");    //never for AIGER
            else if (conflict[0] == mkLit(2*sigsize))
              printf("in fact a (0,*)-clause.\n");    //for AIGER only in reverse mode
            else {
              assert(conflict[0] == mkLit(2*sigsize+1));
              printf("in fact a (*,%d)-clause.\n",phase);  //for AIGER only in normal mode
            }

            return true;
          }
        }
        
        //printf("Dies    | "); ob->print();
        releaseObligation(ob);        
      }
    }

    //printf("clause pushing - phase %d\n",phase);
    
    // clause pushing and the UNSAT-termination check
    for (int i = 1; i < phase; i++) {
      Clauses &layer = *layers[i];
      Solver& solver = *solvers[i];
      
      vec<Lit> assumps;
      assumps.push(mkLit(2*sigsize, false)); 
      assumps.push(mkLit(2*sigsize+1,true));         
      
      int j,k;
      for (j=k=0; j < layer.size(); j++) {
        vec<Lit>& clause = layer[j];
        
        assumps.shrink(assumps.size()-2); // keep the two assumptions
        for (int l = 0; l < clause.size(); l++)
          if (var(clause[l]) > sigsize && var(clause[l]) < 2*sigsize)
            assumps.push(mkLit(var(clause[l])-sigsize,!sign(clause[l])));          
        
        if (solver.simplify(),solver.solve(assumps)) {  //move on
          if (k < i)
            layer[j].moveTo(layer[k]);
          k++;
        } else {  // push forward                   
          solvers[i+1]->addClause(clause);    // could it sometimes happen that we can push a stronger version? (e.g. the conflict guy would be a proper subset?) Test it!
          
          //if (opt_subsume) //didn't seem to be that good - but needs further testing!!!
          //  pruneLayers(clause,i+1,i+1);
          layers[i+1]->push();
          clause.moveTo(layers[i+1]->last());
        }      
      }
      layer.shrink(j-k);

      if (layer.size() == 0) {
        printf("// UNSAT: repetition detected!\n");
        if (opt_verbose) {
                printf("// Delta-layer %d empty!\n",i);
        }
        return true;
      }             
    }

    return false;    
  }
                                                                                               
  void iterativeSearch(Clauses &clauses_goal, Clauses &clauses_rest) {   
    vec<Lit> ma;

    ma.push(mkLit(2*sigsize,  true)); // not (L_initial)
    ma.push(mkLit(2*sigsize+1,true)); // not (L_goal)
    
    called = 0;
      
    if (opt_dot) {
      printf("digraph G {\n");
      printf("graph [size=\"7,10\"];\n");
      printf("node [label=\"\\N\"];\n");         
    }
      
    for (phase = 0; ; phase++) { 
      min_layer = phase;
      max_depth = 0;
    
      if (opt_pphase)
        printf("// Starting phase %d...\n",phase); fflush(stdout);
        
      solvers.push(new Solver());        // adding one new solver
      layers.push(new Clauses());          // adding one new empty layer - not added to unicity (yet)
                                                 // actually, there is alwyas one more layer than would be needed (the zeroth is always empty, though formally it should contain the empty clauses)

      Solver& cur_solver = *solvers.last();
      
      initializeSolver(cur_solver,phase,sigsize);
                
      if (phase == 0)
        for (int j = 0; j < clauses_goal.size(); j++)
          cur_solver.addClause(clauses_goal[j]);
      
      for (int j = 0; j < clauses_rest.size(); j++)
        cur_solver.addClause(clauses_rest[j]);
                      
      if (!cur_solver.simplify()) {
        printf("// UNSAT: unconditionally solved by unit propagation!\n");
        return;
      }

      Obligation *ob = acquireObligation();      
      ob->idx = phase;
      ob->depth = 0;      
      ma.copyTo(ob->ma);
      
      //printf("Toplevel| "); ob->print();
      
      obligations.push(ob);
      
      if (processObligations())
        return; // problem solved                        
    
      if (opt_pphase && opt_verbose) {
        printf("// Max model len: %d/%d%s\n",phase - min_layer,max_depth,min_layer == 0 ? " FULL!" : "");        
        printf("// Pool size: %d\n",poolsize);
        printf("// Ratio: %f (%zu/%d)\n\n",(1.0*clause_ids.size())/in_layers,clause_ids.size(),in_layers);
      
        //printf("Conflicts: %9d\n",conflicts());  
      }         
      
      if (opt_phaselim && phase >= opt_phaselim) {
        printf("// UNRESOLVED: phase limit reached!\n");
        return;
      }      
    }
  }
};

SolvingContext global_context;

void insertClause(SimpSolver &solver, vec<Lit> &clause, int sigsize, bool shifted, Lit litToAdd = lit_Undef) {
  vec<Lit> prepared;
  int shift = shifted ? sigsize : 0;
  
  for (int j=0; j < clause.size(); j++) {
    Lit l = clause[j];  
    prepared.push(mkLit(var(l)+shift,sign(l)));
  }
  
  if (litToAdd != lit_Undef)
    prepared.push(litToAdd);
      
  solver.addClause(prepared); // printClause(prepared);  
}

void analyzeSpec(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {  
  Clauses clauses_goal, clauses_rest;
  
  int new_sigsize;
  
  // preprocessing
  {
    SimpSolver simpSolver;
    
    //TODO: play with these guys -- and with other params if you wish...
    
    //simpSolver.use_asymm = true;    
    //simpSolver.grow = 10; 
  
    //int clause_ids = 0;
    //printf("graph G {\n");
    //printf("size=\"7,10\";\n");  
    
    initializeSolver(simpSolver,-1,sigsize);
     
    //for (int i = 0; i < sigsize; i++) {
    //  printf("\"v%d\" [shape=octagon];\n",i);      
    //}
  
    // initial clauses
    for (int j = 0; j < initial.size(); j++) {           
      insertClause(simpSolver,initial[j],sigsize,true,mkLit(2*sigsize));  // marked as initial
           
    //  vec<Lit> &clause = initial[j];
    //  int cid = clause_ids++;
    //  printf("c%d [color = skyblue,style=filled];\n",cid);      
    //  for (int i = 0; i < clause.size(); i++)
    //    printf("c%d -- \"v%d\"[len=3];\n",cid,var(clause[i]));
    }
        
    // goal clauses        
    for (int j = 0; j < goal.size(); j++) {    
      insertClause(simpSolver,goal[j],sigsize,true,mkLit(2*sigsize+1));   // marked as goal
    
    //  vec<Lit> &clause = goal[j];
    //  int cid = clause_ids++;
    //  printf("c%d [color = red,style=filled];\n",cid);      
    //  for (int i = 0; i < clause.size(); i++)
    //    printf("c%d -- \"v%d\"[len=3];\n",cid,var(clause[i]));         
    }
         
    // universal clauses
    for (int j = 0; j < universal.size(); j++) {       
      insertClause(simpSolver,universal[j],sigsize,true);  //universals are unmarked
      
    //  vec<Lit> &clause = universal[j];
    //  int cid = clause_ids++;
    //  printf("c%d;\n",cid);      
    //  for (int i = 0; i < clause.size(); i++)
    //    printf("c%d -- \"v%d\"[len=5];\n",cid,var(clause[i]));         
    }
    
    // step clauses    
    for (int j = 0; j < step.size(); j++) {    
      insertClause(simpSolver,step[j],0,false,mkLit(2*sigsize,true));  // marked as incompatible with initial
      
    //  vec<Lit> &clause = step[j];
    //  int cid = clause_ids++;
    //  printf("c%d;\n",cid);      
    //  for (int i = 0; i < clause.size(); i++)
    //    printf("c%d -- \"v%d\";\n",cid,var(clause[i]));                 
    }      
      
    // freeze the markers, and all variables from lower signature
    simpSolver.setFrozen(2*sigsize,true);
    simpSolver.setFrozen(2*sigsize+1,true);
    for (int i = 0; i < sigsize; i++) // don't eliminate lower signature variables (it is trivial, and it spoils the statistics)
      simpSolver.setFrozen(i,true);
    for (int j = 0; j < step.size(); j++)
      for (int i = 0; i < step[j].size(); i++)
        if (var(step[j][i])<sigsize) {
          simpSolver.setFrozen(var(step[j][i]),true); // here we do it again, but who cares
          simpSolver.setFrozen(var(step[j][i])+sigsize,true); //and this is the important part
        }
    
    int before = simpSolver.nClauses();    // in fact, we don't see the number of unit clauses here !!!
         
    if (opt_elimination ? !simpSolver.eliminate(true) : !simpSolver.simplify()) {
      printf("// UNSAT: solved by variable elimantion!\n");
      return;
    }
    //printf("eliminated_vars: %d\n",simpSolver.eliminated_vars);
    //printf("sub_subsumed: %d\n",simpSolver.sub_subsumed);
    //printf("sub_deleted_literals: %d\n",simpSolver.sub_deleted_literals);
    //printf("asymm_lits: %d\n",simpSolver.asymm_lits);
    
    Clauses simpClauses;
    simpSolver.copyOutClauses(simpClauses);
    
    int new_var_count = 0;
    vec<Var> renaming;
    
    for (int i = sigsize; i < 2*sigsize+2; i++) { // the two markers didn't get eliminated!
      renaming.push();
      
      if (!simpSolver.isEliminated(i))
        renaming.last() = new_var_count++;
      else
        renaming.last() = var_Undef;      
    }
    
    new_sigsize = new_var_count - 2; //the two markers don't count
    
    if (opt_verbose) {
      printf("// Eliminated %d variables -- new sigsize: %d.\n",simpSolver.eliminated_vars,new_sigsize);
      printf("// Simplified from %d to %d clauses.\n",before,simpSolver.nClauses());          
    }
    
    for (int i = 0; i < simpClauses.size(); i++ ) {
      vec<Lit>& clause = simpClauses[i];

      bool goal = false;
      
      for (int j = 0; j < clause.size(); j++) {
        Lit l = clause[j];
        Var v = var(l);
                
        if (v == 2*sigsize+1) {
          assert(!sign(l));  
          goal = true;
        }
      }
      
      // apply the renaming
      for (int j = 0; j < clause.size(); j++) {
        Lit l = clause[j];
        Var v = var(l);

        if (v < sigsize)
          clause[j] = mkLit(renaming[v],sign(l));
        else {
          clause[j] = mkLit(renaming[v-sigsize]+new_sigsize,sign(l));          
        }            
      }
        
      Clauses& target = (goal ? clauses_goal : clauses_rest);
        
      int idx = target.size();
      target.push();
      clause.moveTo(target[idx]);            
    }
  }
  
  global_context.sigsize = new_sigsize;
  global_context.iterativeSearch(clauses_goal,clauses_rest);  
}

//=================================================================================================

void debug_Spec(int &sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  vec<Lit> cur;
  
  sigsize = 2;
  
  cur.push(mkLit(0,true)); // ~a
  initial.push(cur);
  cur.clear();
  
  cur.push(mkLit(1,false)); // b
  initial.push(cur);
  cur.clear();
  
  cur.push(mkLit(0,false)); // a
  goal.push(cur);
  cur.clear();
  
  cur.push(mkLit(1,false)); // b
  goal.push(cur);
  cur.clear();

  cur.push(mkLit(1,false)); // b
  cur.push(mkLit(1+2,false)); // b'
  step.push(cur);    
  cur.clear();

  cur.push(mkLit(1,true));   // ~b
  cur.push(mkLit(1+2,true)); // ~b'
  step.push(cur);    
  cur.clear();
  
  // making it unsat
  cur.push(mkLit(0,false));   // a
  cur.push(mkLit(0+2,true)); // ~a'
  step.push(cur);    
  cur.clear();
}

void debug_Spec2(int &sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  vec<Lit> cur;
  
  sigsize = 1;
  /*   
  cur.push(mkLit(0,true)); // ~a
  step.push(cur);
  cur.clear();
    
  cur.push(mkLit(0+1,false)); // a'
  step.push(cur);
  cur.clear();
  */
  
  /*
  cur.push(mkLit(0,true)); // ~a
  cur.push(mkLit(1+0,false)); // a'
  step.push(cur);
  cur.clear();      
  */
  
  cur.push(mkLit(0,false)); // a
  initial.push(cur);
  cur.clear();
  
  cur.push(mkLit(0,true)); // ~a
  goal.push(cur);
  cur.clear();   
  
  cur.push(mkLit(0,false)); // a
  goal.push(cur);
  cur.clear();   
}


void test_Spec(int input_size, bool reversed, int &sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  assert(input_size >= 2);

  vec<Lit> cur;
  
  sigsize = input_size;
  
  //initial
  for (int i = 0; i < input_size; i++) {
    cur.push(mkLit(i,true)); // ~ v_i
    if (reversed) 
      goal.push(cur);
    else
      initial.push(cur);
    cur.clear();
  }
  
  //goal
  cur.push(mkLit(0,false)); // v_0
  if (reversed)
    initial.push(cur);
  else
    goal.push(cur);
  cur.clear();
  
  int low  = reversed ? input_size : 0;
  int high = reversed ? 0 : input_size;
  
  //step 
  for (int i = 0; i < input_size-1; i++) {
    cur.push(mkLit(i+low,false));   // v_i
    cur.push(mkLit(i+1+high,true)); // ~v_{i+1}'
    
    step.push(cur);    
    cur.clear();
  }
  
  cur.push(mkLit(input_size-1+low,false));  // v_max
  cur.push(mkLit(0+high,true));             // ~v_0'
  step.push(cur);    
  cur.clear();    
}

void monotonify(int &sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step, bool twisted) {
  vec<Lit> cur;

  // uses the original sigsize value thoughout, but in fact adds two new variables:
  // v_sigsize to have a single clause, single literal goal of the original
  // v_{sigsize+1} as the OK variable to be the new "monotone" goal
    
  //initial ( OK => goal )
  cur.push(mkLit(sigsize,false));    // v_sigsize
  cur.push(mkLit(sigsize+1,true));   // ~v_{sigsize+1}
  initial.push(cur);
  cur.clear();
  
  // universals stay untouched + extended old goal clauses are added
  for (int i = 0; i < goal.size(); i++) {
    goal[i].moveTo(cur);
    cur.push(mkLit(sigsize,true)); // ~v_sigsize
    universal.push(cur);
    cur.clear();
  }
  goal.clear();
  
  // just one new goal clause ( OK )
  cur.push(mkLit(sigsize+1,false));  // v_{sigsize+1}  
  goal.push(cur);
  cur.clear();
  
  //translate the step clauses
  for (int i = 0; i < step.size(); i++) {
    vec<Lit>& clause = step[i];
    for (int j = 0; j < clause.size(); j++)
      if (var(clause[j])>=sigsize)
        clause[j] = mkLit(var(clause[j])+2,sign(clause[j]));
  }
  
  //and add the final one ( OK' => goal' | OK )
  cur.push(mkLit(sigsize+1+(twisted ? sigsize+2 : 0),false));    //  v_{sigsize+1}  
  cur.push(mkLit(sigsize+1+(twisted ? 0 : sigsize+2),true));     // ~v_{sigsize+1}'
  cur.push(mkLit(sigsize  +(twisted ? 0 : sigsize+2),false));    // v_sigsize'
  step.push(cur);
  cur.clear();
  
  // enlarge the signature:
  sigsize++;
  sigsize++;
}

static void SIGINT_exit(int signum) {
  printf("//*** INTERRUPTED ***\n");
  if (opt_verbose)
    global_context.printStat();  
  fflush(stdout);
  _exit(1); 
}

int main(int argc, char** argv)
{
    try {
      setUsageHelp("USAGE: %s [options] <aiger-input-file>\n\n");

#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        // printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif

    // THE SPEC:
    int sigsize; 
    Clauses initial;
    Clauses goal;
    Clauses universal;
    Clauses step;

    parseOptions(argc, argv, true);

    assert(!opt_reversed); /*NOT REVERSED is OBLIGATORY - otherwise it is not monotone*/
    
    aiger_LoadSpec((argc == 1) ? 0 : argv[1], (int)opt_reversed, (int)opt_pg, (int)false, opt_kth_property, (int)false,
                   sigsize,initial,goal,universal,step);

    //test_Spec(20,(int)opt_reversed,sigsize,initial,goal,universal,step);    
    //debug_Spec2(sigsize,initial,goal,universal,step);

    if (opt_verbose)
      printf("// Loaded spec -- sigsize: %d, #initial: %d, #goal: %d, #universal: %d, #step: %d\n",sigsize,initial.size(),goal.size(),universal.size(),step.size());
       
    assert(opt_monot & 1); // THIS IS OBLIGATORY IN OUR VERSION IC3, because we don't check for interesection with initial / bad
    
    if (opt_monot & 1) {        
      monotonify(sigsize,initial,goal,universal,step,false);    
    
      if (opt_verbose)
        printf("Made backward monotone -- sigsize: %d, #initial: %d, #goal: %d, #universal: %d, #step: %d\n",sigsize,initial.size(),goal.size(),universal.size(),step.size());
    }
    
    if (opt_monot & 2) {
      monotonify(sigsize,goal,initial,universal,step,true);    
    
      if (opt_verbose)
        printf("Made forward monotone -- sigsize: %d, #initial: %d, #goal: %d, #universal: %d, #step: %d\n",sigsize,initial.size(),goal.size(),universal.size(),step.size());
    }

    signal(SIGINT, SIGINT_exit);
    analyzeSpec(sigsize,initial,goal,universal,step);

    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("OutOfMemory!\n");
        exit(0);
    }
}

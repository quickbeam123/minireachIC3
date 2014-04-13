/*****************************************************************************************[Main.cc]
Copyright (c) 2013, Martin Suda
Max-Planck-Institut für Informatik, Saarbrücken, Germany
 
minireachIC3 sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
minireachIC3 are exactly the same as Minisat on which it is based on. (see below).

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

#include "core/MarkingSolver.h"
#include "core/ClauseSet.h"

#include "simp/SimpSolver.h"
#include "core/Aiger2Spec.h"

#include "core/clock.h"

#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <deque>

using namespace Minisat;

static StringOption opt_format  ("INPUT", "format", "Input format: currently either <aiger> or <dimspec>. Default <aiger>.", "aiger");

static BoolOption opt_verbose     ("PARSE", "v", "Verbose output.", true);
static BoolOption opt_pphase     ("MAIN", "pphase", "Print phase.", false);

static BoolOption opt_pg          ("PARSE", "pg","Plaisted-Greenbaum CNF encoding.", true);
static IntOption  opt_kth_property("PARSE", "id","Pick a particular property from Multi-Property input (indexing from 0).\n"
                                                 "-1 picks the only one and aborts if there is no such.\n"
                                                 "-2 just prints the ids of all available and aborts", -1, IntRange(-2, INT32_MAX));

static BoolOption opt_reversed    ("PARSE", "rev", "Swap initial and goal formulas after parsing.", true);
static BoolOption opt_elimination ("MAIN", "simp", "Perform variable elimination before actual solving.", true);

static IntOption opt_phaselim ("MAIN", "phaselim", "Terminate after a given number of phases.", 0, IntRange(0,INT32_MAX));

static BoolOption opt_obligqueue("MAIN", "oblqueue", "Store obligations FIFO-style. (as opposed to LIFO).", false); 

static BoolOption opt_earlystop ("MAIN", "earlystop", "Don't put weak clauses into strong layers.", true); // seems to be a good idea after all

static IntOption opt_resched ("MAIN", "resched", "Reschedule obligations (allows long models).", 1, IntRange(0,3));

static BoolOption opt_statpushing("STAT", "spushing", "Print pushing statistics.", true);
static BoolOption opt_statclauses("STAT", "sclauses", "Print layer clause statistics.", true);
static BoolOption opt_statobligations("STAT", "sobligations", "Print model statistics.", true);
static BoolOption opt_statmodel("STAT", "smodel", "Print model statistics.", true);
static BoolOption opt_statlayer("STAT", "slayer", "Print layer statistics.", true);
static BoolOption opt_sminim("STAT", "sminim", "Print clause minimization statistics.", true);
static BoolOption opt_sttime("STAT", "stime", "Print time statistics.", true);

static IntOption opt_startphase("MAIN", "startphase", "Initial phase to start with (may become incomplete for non-monot designs).", 0, IntRange(0,INT32_MAX));

static BoolOption opt_minimize ("MAIN", "min", "(Inductively) minimize learned clauses.", true); 
static IntOption opt_induction ("MAIN", "ind", "Use induction for minimization (1 = one pass, 2 = iterate until fixpoint).", 2, IntRange(0,2)); 

static BoolOption opt_print_solution ("MAIN", "psol", "Print the solution assignment (for dimspec format inputs).", false);

//=================================================================================================

void printVec(const vec<int>& v) {
  for (int i = 0; i < v.size(); i++)
    printf("%d, ",v[i]);
  printf("\n");
}

void printLit(Lit lit) {
  printf("%s%d ",sign(lit)?"-":"",var(lit));
}

void printClause(const vec<Lit> &clause, const vec<int> &markers) {
  for (int i = 0; i < clause.size(); i++) 
    printLit(clause[i]);    
  
  printf(" || ");
  
  for (int i = 0; i < markers.size(); i++)      
    printf("%d ",markers[i]);
      
  printf("\n");
}

void printIStars(int i) {
  for (int j = 0; j < i; j++)
    printf("*");
  printf("\n");
}

//=================================================================================================

#define ABSTRACTION_TYPE  uint32_t
#define ABSTRACTION_BITS  (31)

ABSTRACTION_TYPE calcAbstraction(vec<Lit> const & data) {
  ABSTRACTION_TYPE res = 0;
  for (int i = 0; i < data.size(); i++)
    res |= 1 << (var(data[i]) & ABSTRACTION_BITS);
  return res;
}

//=================================================================================================


struct Obligation {
  int depth;
  
  Obligation *next; // used for parent pointers for active obligations (which is later used for reconstructing the witness)
  
  vec<Lit> ma;
  ABSTRACTION_TYPE abs; // abstraction of the above
  
  Obligation(int d, Obligation* n) : depth(d), next(n) {}
};

static int ids = 0;

/* wrapper for layer clauses and their witness */
struct CWBox {
  int id;

  vec<Lit> data;         // for clause the actual literals, for witness the negated state as a clause
  ABSTRACTION_TYPE abs;  // abstraction of the above
  
  CWBox*  other;  // the other of the two
  
  CWBox*  next;    // to form a linked list  
  CWBox** prev;    // to delete from anywhere
  
  CWBox() : abs(0), other(0), next(0), prev(0) { id = ids ++; }
  CWBox(ABSTRACTION_TYPE a, vec<Lit> const & d) : abs(a), other(0), next(0), prev(0) { d.copyTo(data); id = ids ++; } 
    
  void integrate(CWBox** holder) {  // like insert
    assert(holder);
    next = *holder;
    *holder = this;
    prev = holder;
    if (next) {
      assert(next->prev == holder);
      next->prev = &next;
    }    
  }
     
  void disintegrate() {             // like remove 
    assert(prev);
    assert(*prev == this);
    *prev = next;
    if (next) {
      assert(next->prev == &next);      
      next->prev = prev;
    }
  }
  
  void relocate(CWBox** holder) {   // like move (with all the guys below)        
    // similar to first half of disintegrate
    assert(prev);
    assert(*prev == this);
    *prev = 0;
  
    // similar to first half of integrate
    assert(holder);
    *holder = this;
    prev = holder;
  }
  
};

void printCWBox(CWBox* box) {
  while (box) {
    if (box->next) {
      assert(box->next->prev == &box->next);    
    }    
    printf("%d -> ",box->id);
    
    box = box->next;
  }
  
  printf("\n");
}

// a wrapper for vec< CWBox* > that repairs prev pointers in all the members if reallocation happens
struct CBoxVec {
  vec< CWBox* > data;

  CWBox* const & operator [] (int index) const { return data[index]; }
  CWBox* &       operator [] (int index)       { return data[index]; }
  
  int  size(void) const   { return data.size(); }  
  void push(void) {
    data.push(0);
    
    // could reallocate - repair the pointers!!!
    for (int i = 0; i < data.size(); i++)
      if (data[i])
        data[i]->prev = &data[i];
  }  
};

typedef std::deque<Obligation*> OblDeque;

struct SolvingContext {  
  Lit goal_lit;
  bool artificial_goal_var;
  int sigsize;

  Clauses goal_clauses;
  Clauses rest_clauses;
  
  Clauses model_path;  // filled in at the end in the case of SAT (i-th element with satisfy L_i, in particulat the 0-th state will be the goal state)
  
  vec<bool> bridge_variables; 
  // TODO: this idea should be extended up to the point where the low signature part of the solver is only as big as the bridge (the rest of the variables are just rubbish!)
  // Well, in general this is a little more complicated: remember there is S_in, S_out, and S_reg in the  Niklases' paper -- the low signature should contain S_in and S_reg

  int phase;
  
  vec<MarkingSolver*> solvers;
  
  CBoxVec layers;         // here sit the clauses   
  CBoxVec push_requests;  // and here
  CBoxVec witnesses;      //  or here their respective bros
   
  vec< OblDeque > obligations;
        
  // statistics
  int pushing_request;
  int pushing_nontriv_request;
  int pushing_success;
  
  int oblig_processed;
  int oblig_subsumed;
  int oblig_sat;
  int oblig_unsat;
  int oblig_resched_clause;
  int oblig_resched_subs;   
  
  int clauses_dersolver;
  int clauses_univ;
  int clauses_strengthened;         
     
  int solver_call_extension;
  int solver_call_push;
  
  int minim_attempts;  
  int minim_solver;
  int minim_explicit;
  int minim_push;
    
  int model_min_layer;
  int model_max_depth;   
     
  SolvingContext() : phase(-1),
                     pushing_request(0), pushing_nontriv_request(0), pushing_success(0),
                     oblig_processed(0), oblig_subsumed(0), oblig_sat(0), oblig_unsat(0), oblig_resched_clause(0), oblig_resched_subs(0),                                                                                                        
                     clauses_dersolver(0), clauses_univ(0), clauses_strengthened(0),                                         
                     solver_call_extension(0), solver_call_push(0),                     
                     minim_attempts(0), minim_solver(0), minim_explicit(0), minim_push(0),
                     model_min_layer(0), model_max_depth(0),                       
                     called(0),
                     initial_obligation(0,0)
  { }    

  void deleteClause(CWBox *cl_box) {
    if (cl_box->other) {
      cl_box->other->disintegrate();
      delete cl_box->other;
    }
    cl_box->disintegrate();
    delete cl_box;
  }
  
  ~SolvingContext() {
    if (opt_verbose)
      printGOStat();      

    for (int i = 0; i < obligations.size(); i++)
      for (OblDeque::iterator it = obligations[i].begin(); it != obligations[i].end(); ++it)
        delete (*it);
      
    for (int i = 0; i < layers.size(); i++)
      while (layers[i])
        deleteClause(layers[i]);

    for (int i = 0; i < solvers.size(); i++)
      delete solvers[i];     
  }
  
  void printStat(bool between_phases = false) {
    if (opt_statpushing) {
      printf("\nClause pushing:\n");                     
      printf("\t%d requests handled.\n",pushing_request);
      printf("\t%d proper - %d clauses pushed.\n", pushing_nontriv_request,pushing_success);                     
    
      pushing_request = 0;     
      pushing_nontriv_request = 0;
      pushing_success = 0;      
    }
       
    if (opt_statobligations) {
      printf("\nObligations:\n");
      printf("\t%d processed,\n",oblig_processed);
      printf("\t%d extended,\n",oblig_sat);
      printf("\t%d blocked,\n",oblig_unsat);    
      printf("\t%d subsumed,\n",oblig_subsumed);
      printf("\t%d rescheduled due to clause,\n",oblig_resched_clause);
      printf("\t%d rescheduled due to subsumption.\n",oblig_resched_subs);      
           
      //printf("   maoccursz: %zu\n",mas.size());
      
      oblig_processed = 0;
      oblig_subsumed = 0;            
      oblig_sat = 0;
      oblig_unsat = 0;      
      oblig_resched_clause = 0;
      oblig_resched_subs = 0;
    }  
  
    if (opt_statclauses) {
      printf("\nClauses:\n");
      printf("\t%d derived by solver (%d universals), subsumed %d.\n",clauses_dersolver,clauses_univ,clauses_strengthened);
      
      int inlayers = 0;
      int length_max = 0;
      int length_sum = 0;
           
      for (int i = 1; i <= phase+1; i++) {                    
        for (CWBox* cl_box = layers[i]; cl_box != 0; cl_box = cl_box->next) {
          vec<Lit> const & clause = cl_box->data;
                             
          if (clause.size() > length_max)
            length_max = clause.size();            
          length_sum += clause.size();
          inlayers += 1;                
        }
      }

      printf("\tKept: %d ",inlayers);
      printf("(max %d lits, %f lits on average).\n",length_max, (1.0*length_sum)/inlayers);

      clauses_dersolver = 0;
      clauses_univ = 0;  
      clauses_strengthened = 0;      
    }       
    
    if (opt_minimize && opt_sminim) {
      printf("\nMinimization averages from %d attempts:\n", minim_attempts);
      printf("\t%f by solver,\n",(1.0*minim_solver)/minim_attempts);      
      printf("\t%f by picking,\n",(1.0*minim_explicit)/minim_attempts);
      printf("\t%f by pushing.\n",(1.0*minim_push)/minim_attempts);
            
      minim_attempts = 0;
      minim_solver = 0;      
      minim_explicit = 0;
      minim_push = 0;    
    }
    
    if (opt_statmodel && between_phases) {
      printf("\nModel: ");
      printf("Length %d, depth %d%s\n",model_max_depth,phase - model_min_layer,model_min_layer == 0 ? " FULL!" : ".");
      
      model_min_layer = phase+1;
      model_max_depth = 0;
    }
  
    if (opt_statlayer) {
      printf("\nLayers: ");
      for (int i = 0; i <= phase+1; i++) {
        int sz = 0;
        for (CWBox* cl_box = layers[i]; cl_box != 0; cl_box = cl_box->next, sz++);         
        printf("%d%s%s",sz,(i == phase+1) ? "]" : "|",(i == phase) ? "[" : "");
      }
      printf("\n");
      
      printf("Avg sz: ");           
      for (int i = 0; i <= phase+1; i++) {
        int sz = 0;
        int lensum = 0;
        for (CWBox* cl_box = layers[i]; cl_box != 0; cl_box = cl_box->next) {
          sz++;
          lensum += cl_box->data.size();
        }
        if (sz)
          printf("%d%s%s",lensum/sz,(i == phase+1) ? "]" : "|",(i == phase) ? "[" : "");
        else
          printf("-%s%s",(i == phase+1) ? "]" : "|",(i == phase) ? "[" : "");                        
      }
      
    } 

    if (opt_sttime) {
      clock_StopAddPassedTime(clock_MAIN);
    
      printf("\nTime:\n");
      printf("\tspent in solver extending %fsec (%f call per sec on average)\n",clock_GetAkku(clock_SOLVER_EXTEND),solver_call_extension/clock_GetAkku(clock_SOLVER_EXTEND));
      printf("\tspent in solver pushing   %fsec (%f call per sec on average)\n",clock_GetAkku(clock_SOLVER_PUSH),solver_call_push/clock_GetAkku(clock_SOLVER_PUSH));
      printf("\tspent in main   %fsec.\n",clock_GetAkku(clock_MAIN));
      
      clock_InitCounter(clock_MAIN);
      clock_StartCounter(clock_MAIN);
      clock_InitCounter(clock_SOLVER_EXTEND);
      clock_InitCounter(clock_SOLVER_PUSH);
      
      solver_call_extension = 0;
      solver_call_push = 0;
    }
   
  }  
  
  void printGOStat() {
    printf("// Game over during phase: %d.\n",phase);   
           
    if (phase >= 0)
      printStat();             
/*     
    for (int i = 0; i <= phase+1; i++)  {
      printf("Layer %d\n",i);    
      for (JustClauseSet::Iterator it = layers[i]->getIterator(); it.isValid(); it.next()) {
        printLits(it.getClause()); 
        printf("\n");      
      }
    }
  */  
    if (opt_sttime) {
      clock_StopPassedTime(clock_OVERALL);
    
      printf("\nGlobal time:\n");
      printf("\tspent on parsing %fsec\n",clock_GetAkku(clock_PARSE));
      printf("\tspent on simplif %fsec\n",clock_GetAkku(clock_SIMP));
      printf("\t    overall      %fsec.\n",clock_GetAkku(clock_OVERALL));    
    }     
  }

  // TODO: keep?  
  /*
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
  */
      
  static const int inductive_layer_idx;
  static const int assumption_mark_id;  
  
  vec<int> marks_tmp;
  
  // INPUT for callSolver()
  vec<Lit> filtered_ma;        // ma without non-bridge variables
  
  // OUTPUT from callSolver()
  vec<Lit> conflict_out;
  int      target_layer_out;  
  
  // temporaries of callSolver
  vec<int> minimark_in;
  vec<int> minimark_out;
  vec<int> rnd_perm;  
   
  int called; 
   
  bool callSolver(int index, CLOCK_CLOCKS cc,       // calls the index-th solver, under then give assumptions filtered_ma plus the layer assumptions
                  bool compute_conflict,          // request for returning (minimized, if flag set) appropriate conflict clause (to be delivered in conflict_out), 
                                                  // also, target_layer_out will containt index of the least delta layer on which the conflict depends (or inductive_layer_idx for "infty")
                  bool induction) {               // allow using induction during minimization
                                                           

    MarkingSolver& solver = *solvers[index];

    //printf("Calling for solver %d with ma ",index); printLits(filtered_ma);
                 
    clock_StopAddPassedTime(clock_MAIN);
    clock_StartCounter(cc);   
    
    minimark_in.clear();
    for (int i = index; i <= phase; i++)
      minimark_in.push(i);
    minimark_in.push(inductive_layer_idx);
    minimark_in.push(assumption_mark_id);
    
    solver.preprocessAssumptions(filtered_ma,minimark_in);    
    bool result = (solver.simplify(),solver.solve());
    
    if (!result && compute_conflict) {
      solver.preprocessConflict(conflict_out,minimark_out);
    
      if (opt_minimize) {
        minim_attempts++;
      
        minim_solver += filtered_ma.size() - conflict_out.size();
                                 
        //turn the conflict clause back to assumptions
        for (int i = 0; i < conflict_out.size(); i++)
          conflict_out[i] = ~conflict_out[i];                                      
        solver.preprocessAssumptions(conflict_out,minimark_in);
        Lit indy = solver.getAssump(conflict_out.size() + minimark_in.size() - 2); // the translation of the induction marker, which we never plan to remove
        int assy_idx = conflict_out.size() + minimark_in.size() - 1;
        Lit assy = solver.getAssump(assy_idx); // the translation of the assumption marker, which we never plan to remove
        int size = conflict_out.size();
                      
        //generate random permutation
        rnd_perm.clear(); 
        for (int i = 0; i < size; i++)
          rnd_perm.push(i);
        for (int i = size-1; i > 0; i--) {
          int idx = rand() % (i+1);
          int tmp = rnd_perm[idx];
          rnd_perm[idx] = rnd_perm[i];
          rnd_perm[i] = tmp;                   
        }        
                
        bool removed_something;
        int cycle_count = 0;
        do {                 
          removed_something = false;
          
          // one pass:
          for (int i = 0; i < size; i++) {
            int idx = rnd_perm[i];
            Lit save = solver.getAssump(idx);
            if (save == indy) // already removed in previous passes
              continue;

            solver.setAssump(idx,indy);  // one assumption effectively removed (since replaced by indy)
            
            if (induction && opt_induction) {  // inductively assume the current conflict clause            
              //abusing conflict_out for that
              conflict_out.clear();
              for (int i = 0; i < size; i++) {
                Lit l = solver.getAssump(i);
                if (l != indy && var(l) < sigsize)
                  conflict_out.push(mkLit(var(l)+sigsize,!sign(l)));   // negate back and shift
              }
              conflict_out.push(goal_lit);                       
              
              marks_tmp.clear();
              marks_tmp.push(assumption_mark_id); 
              solver.addClause(conflict_out,marks_tmp);
            }
          
            if (solver.simplify(),solver.solve()) {
              solver.setAssump(idx,save);  // put the literal back

              if (induction && opt_induction) {
                solver.invalidateMarker(assumption_mark_id); // efectively delete the assumed clause                
                assy = mkLit(solver.ensureMarkerRegistered(assumption_mark_id),true); // immediately claim it again (the same id, but a new var!) and make a lit out of it
                solver.setAssump(assy_idx,assy);  // assume the new guy from now on
              }
              
            } else {              
              minim_explicit++;
              removed_something = true;
            }
          }
          cycle_count++;
        } while (induction && (opt_induction>1) && removed_something);       
        
        // "pushing"         
        target_layer_out = index;        
        for (int i = 0; i < minimark_in.size()-2; i++) {
          solver.setAssump(size + i, indy);
          if (solver.simplify(),solver.solve())
            break;
          target_layer_out = minimark_in[i+1]; //makes sense even with inductive_layer_idx, which is the last but one value       
          minim_push++;
        }       
                     
        // prepare final version of conflict_out        
        conflict_out.clear();
        for (int i = 0; i < size; i++) {
          Lit l = solver.getAssump(i);
          if (l != indy)
            conflict_out.push(~l);     // negate back 
        }                          
        
        // cleanup
        if (induction && opt_induction)
          solver.invalidateMarker(assumption_mark_id);
          
      } else {
        target_layer_out = inductive_layer_idx;                           
        for (int i = 0; i < minimark_out.size(); i++)
          if (minimark_out[i] < target_layer_out) // relying on (inductive_layer_idx < assumption_mark_id)
            target_layer_out = minimark_out[i];      
      }
    }
           
    clock_StopAddPassedTime(cc);
    clock_StartCounter(clock_MAIN);   
           
    // Master check    
    /*
    if (!result && induction && compute_conflict) {
      // part one
      vec<Lit> conflict;
        
      for (int i = 0; i < conflict_out.size(); i++)
        conflict.push(~conflict_out[i]);      
      sort(conflict);
                          
      assert(subsumes(conflict,filtered_ma));                
      
      //part two
      MarkingSolver test_solver;
      test_solver.initilazeSignature(2*sigsize+1);  
      vec<int> marker; //empty -- we don't care about depedancy
      for (int i = 0; i < rest_clauses.size(); i++)
        test_solver.addClause(rest_clauses[i],marker);
      
      int from_layer = target_layer_out;        
      if (from_layer == 0) {
        for (int i = 0; i < goal_clauses.size(); i++)
          test_solver.addClause(goal_clauses[i],marker);          
        from_layer = 1;          
      }

      if (from_layer == inductive_layer_idx) 
        from_layer = phase+1;
      
      for (int l = from_layer; l <= phase+1; l++)
        for (JustClauseSet::Iterator it = layers[l]->getIterator(); it.isValid(); it.next())       
          test_solver.addClause(it.getClause(),marker);

      // the clause itself -- shouldn't be necessary without induction
      if (opt_induction) {
        vec<Lit> the_clause;
                
        for (int i = 0; i < conflict_out.size(); i++) {
          if (var(conflict_out[i]) == 2*sigsize) {
            assert(sign(conflict_out[i]));
            // the step clause marker doesn't go into learned clauses
          } else {
            assert(var(conflict_out[i])<sigsize);
            Lit lit = mkLit(var(conflict_out[i])+sigsize,sign(conflict_out[i]));
            the_clause.push(lit);            
          }
        }        
        the_clause.push(goal_lit);  
        sort(the_clause);  
                       
        test_solver.addClause(the_clause,marker);
      }
      
      test_solver.preprocessAssumptions(conflict,marker);      
      assert(!(test_solver.simplify(),test_solver.solve()));      
    }
    */
         
    return result;
  }  
  
  bool absSubsumes(ABSTRACTION_TYPE a1, ABSTRACTION_TYPE a2) {
    return (a1 & ~a2) == 0;
  }
  
  /*
     A new clause should enter a layer. Subsume all the guys that are there (the new could could get subsumed as well).
  */
  int pruneLayerByClause(ABSTRACTION_TYPE abs, vec<Lit>const & clause, int idx, bool testForWeak = true) {
    // frees subsumed clauses in layer
    int res = 0; //returns the number of subsumed guys and -1 if the argument was subsumed (and testForWeak was true)       
    
    for (CWBox* layer_box = layers[idx]; layer_box != 0; /* update inside */) {
      if (absSubsumes(abs,layer_box->abs) && subsumes(clause,layer_box->data)) {
        CWBox* tmp_box = layer_box;
        layer_box = layer_box->next;
        //printf("subsumed clause %d\n",tmp_box->id); 
        deleteClause(tmp_box);
        res++;
      } else if (testForWeak && absSubsumes(layer_box->abs,abs) && subsumes(layer_box->data,clause)) {
        //printf("subsumed by %d\n",layer_box->id);        
        assert(res == 0);        
        return -1;
      } else {
        layer_box = layer_box->next;
      }
    }
                
    return res;
  }
     
  /* 
    A new strong clause is coming to this layer, maybe some obligations will be pushed back.
    (not killed, actually, they all wait for the phase to be over, since they could be somebody's parents)
  */
  int pruneObligations(ABSTRACTION_TYPE abs,
                       vec<Lit>const & clause,   //the potentially subsuming clause
                       int from,                 //the position to work on (if out of bounds, just no-op)
                       int relocate_to) {        //the first index where they can live (if out of bounds, just kick them out)
    if (from > phase)
      return 0;

    if (relocate_to > phase+1)
      relocate_to = phase+1;
      
    int res = 0;
    OblDeque& obligs = obligations[from];
    
    OblDeque::iterator it,jt;
    for (it = jt = obligs.begin(); it != obligs.end(); ++it) {
      vec<Lit> &ma = (*it)->ma;
            
      assert(clause_sorted(ma));
    
      // note that as we store the goal_lit in all clauses in layers,
      // this subsumption check only ever works because goal_lit is part of the bridge
      // (and all the generated ma's don't satisfy the goal -- otherwise we would terminate with SAT)
      
      if (absSubsumes(abs,(*it)->abs) && subsumes(clause,ma)) {
        res++;
        
        if (opt_resched) { 
          obligations[relocate_to].push_back(*it);          
          oblig_resched_subs++;                                         
        } else
          delete (*it);
      } else  // keeping it here
        *jt++ = *it;
    }
    obligs.erase(jt,obligs.end());
  
    return res;
  }
  
  /* 
    A new strong clause is coming to this layer, so it could initiate some pushing by killing a witness.
  */
  int pruneWitnesses(ABSTRACTION_TYPE abs,
                     vec<Lit>const & clause,   //the potentially subsuming clause
                     int from) {  
    if (from > phase)
      return 0;
    
    int res = 0;
    
    for(CWBox* wit_box = witnesses[from]; wit_box != 0; /*iteration inside*/) {
      if (absSubsumes(abs,wit_box->abs) && subsumes(clause,wit_box->data)) { // clause will need a new witness
        CWBox* tmp_box = wit_box;
        wit_box = wit_box->next;
        
        res++;
        
        tmp_box->disintegrate();
        tmp_box->integrate(&push_requests[from]);
      } else {
        wit_box = wit_box->next;
      }    
    }
    
    return res;
  }
  
  /*
    a new clause (either just derived or pushed) is coming to this clause
  */
  void handleNewClause(int target_layer, int first_questionable, int upmost_layer, ABSTRACTION_TYPE abs, vec<Lit> const & clause, vec<int> const& markers) {  
    int stopped = 0;    
    int sum_cl_killed = 0;
    int sum_ob_pushed = 0;
    //printf("Inserting %s-clause to layer %d to kill ma in layer %d. ",target_layer <= phase ? "N" : "U",target_layer,first_questionable+1);
           
    for (int i = target_layer; i >= upmost_layer; i--) {
      if (!stopped) {    
        int res = pruneLayerByClause(abs,clause,i,/* maybe_weak (?)*/ i <= first_questionable /* otherwise don't test forward */ );
                                    
        if (res < 0) { //got subsumed here; will not subsume anymore
          assert(i < target_layer);                 // got inserted into his target layer
          assert(i <= first_questionable);          // should be strong even up to this point
          stopped = i;
          // printf("Killed in %d. ",i);                   
          
          if (opt_earlystop) // true by default!
            return;          
        } else {
          clauses_strengthened += res;
          sum_cl_killed += res;
          // printf("Kills %d in %d. ",res,i);
          
          int obl_res = pruneObligations(abs,clause,i,target_layer+1); // the new clause is still strong, could it kill/push some obligations here?
          sum_ob_pushed += obl_res;
          oblig_subsumed += obl_res;
          
          int wit_res = pruneWitnesses(abs,clause,i);
        }
      }
                 
      if (i <= phase) {// just because of the case with universal clauses, when the insertion is into the inductive layer of index phase+1
        solvers[i]->addClause(clause,markers);                      
      }
      // we could also stop inserting when stopped is identified, but sometimes the weak clauses in "strong" solvers will allow for better inductive minimization (thanks to their weak marker)
    }
    
    //printf("Killed %d, went %d steps deep and subsumed %d obligations\n",sum_cl_killed,target_layer-stopped,sum_ob_pushed);    
  }
      
  /* 
    new clause, push clause, or a clause with a killed witness is looking for new one
  */
  void lookForWitness(CWBox * cl_box, int index) {
    vec<Lit> & clause = cl_box->data;
   
    solver_call_push++;    
    pushing_request++;
    if (cl_box->other->data.size())
      pushing_nontriv_request++;
      
    filtered_ma.clear();
    for (int l = 0; l < clause.size(); l++) {
      assert(var(clause[l]) >= sigsize);
      filtered_ma.push(mkLit(var(clause[l])-sigsize,!sign(clause[l])));      
    }
    filtered_ma.push(mkLit(2*sigsize, false));                   
    
    if (callSolver(index,clock_SOLVER_PUSH,false,false)) {
      MarkingSolver &model_solver = *solvers[index];      
      
      // extract the witness
      vec<Lit> & ma = cl_box->other->data;
      ma.clear();      
      //like when extracting ma normally
      for (int j = 0; j < sigsize; j++) {
        assert(model_solver.model[j+sigsize] != l_Undef);  
        if (bridge_variables[j])                                              
          ma.push(mkLit(j+sigsize,model_solver.model[j+sigsize] == l_True));  //but it stays in upper signature and unnegated
      }
      // and we don't add the initial marker
      cl_box->other->abs = calcAbstraction(ma);      
      
      cl_box->other->integrate(&witnesses[index]);
    } else {     // pushed
      marks_tmp.clear();
      marks_tmp.push(index+1);
    
      pushing_success++;
    
      handleNewClause(index+1,index+1,index+1,cl_box->abs,clause,marks_tmp); /* it should not get subsumed there! */
    
      cl_box->disintegrate();
      cl_box->integrate(&layers[index+1]);
      cl_box->other->integrate(&push_requests[index+1]);                                        
    }
  }
  
  Obligation initial_obligation;
  
  bool processObligations() {
    int obl_top = phase + 1;  // the lowest index where there is possibly any obligation to look for    
  
    for (;;) {
      // first do all the necessary pushing 
      // (TODO: maybe stop before the current value of obl_top?)
      // (TODO: maybe keep note of where from it makes sense to start looking for push_requests?)      
      for (int i = 1; i < phase /*cannot push from L_{phase}, there is not L_{phase+1} yet*/; i++) {
        while (push_requests[i]) {
          CWBox* req_box = push_requests[i];
          req_box->disintegrate();
          lookForWitness(req_box->other,i);
        }
        
        if (layers[i] == 0) {
          printf("// UNSAT: repetition detected!\n");
          if (opt_verbose)
            printf("// Delta-layer %d emptied by pushing!\n",i);            
          return true;
        }
      }
      
      // now handle obligations
      Obligation* ob;
      while (obl_top <= phase && obligations[obl_top].size() == 0)
        obl_top++;      
        
      if (obl_top > phase) {
        ob = &initial_obligation;        
      } else {
        if (opt_obligqueue) {
          ob = obligations[obl_top].front();        
          obligations[obl_top].pop_front();
        } else {
          ob = obligations[obl_top].back();        
          obligations[obl_top].pop_back();
        }
      }

      int model_idx = obl_top-1;
      vec<Lit> &our_ma = ob->ma;         

      oblig_processed++;

      // printf("Obligation with model_idx %d.\n",model_idx);
            
      if (model_idx < model_min_layer)
        model_min_layer = model_idx;
    
      if (ob->depth > model_max_depth)
        model_max_depth = ob->depth;

      solver_call_extension++;
    
      filtered_ma.clear();
      for (int i = 0; i < our_ma.size(); i++) {
        assert(var(our_ma[i]) >= sigsize);
        if (var(our_ma[i]) < 2*sigsize) { 
          if (bridge_variables[var(our_ma[i])-sigsize])
            filtered_ma.push(mkLit(var(our_ma[i])-sigsize,!sign(our_ma[i])));
        } else 
          filtered_ma.push(our_ma[i]);               
      }
        
      if (callSolver(model_idx,clock_SOLVER_EXTEND,
                    true,                                  // return conflict
                    obl_top<=phase )                       // induction is not correct for the initial call
                    ) {
        oblig_sat++;             

        //printf("Extended\n");
        
        // going forward        
        Obligation* new_ob = new Obligation(ob->depth+1,ob);
        int new_top;
        
        if (opt_resched == 3)
          new_top = 1; //fast forward
        else if (opt_resched == 2)
          new_top = (model_idx == 1) ? 1 : model_idx-1; // a little forward
        else
          new_top = model_idx;               

        // printf("%d points to %d\n",new_ob->id,ob->id);
        
        MarkingSolver &model_solver = *solvers[model_idx];
        
        vec<Lit>& ma = new_ob->ma;
        ma.clear();
        for (int j = 0; j < sigsize; j++) {
          assert(model_solver.model[j+sigsize] != l_Undef); 
          // normally, the bridgevar trick would go here, but we need to keep the whole model for printing
          ma.push(mkLit(j+sigsize,model_solver.model[j+sigsize] == l_True));
        }                                            
        // only after the previous, so that it is sorted
        ma.push(mkLit(2*sigsize, false)); // L_initial assumed true => turning on step clauses, turning off initial clauses
        new_ob->abs = calcAbstraction(ma);

        if (ob->depth > 0)   // the initial guy is never stored
          obligations[obl_top].push_back(ob);
        obligations[new_top].push_back(new_ob);
        
        obl_top = new_top; // follow him forward       
                
        if (model_idx == 0) {          
          printf("// SAT: model of length %d found:\n",ob->depth+1);

          Obligation* top_ob = new_ob;
          do {
            assert(top_ob);
            model_path.push();
            vec<Lit> & in_ma = top_ob->ma;
            vec<Lit> & out_ma = model_path.last();            
            for (int i = 0; i < in_ma.size(); i++) {
              assert(var(in_ma[i]) >= sigsize);                    
              if (var(in_ma[i]) < 2*sigsize)
                out_ma.push(mkLit(var(in_ma[i])-sigsize,!sign(in_ma[i])));
              else 
                out_ma.push(in_ma[i]);               
            }            
            
            top_ob = top_ob->next;
          } while (top_ob->depth > 0);
          
          assert(top_ob);
          assert(top_ob == &initial_obligation); //this one doesn't go in any more
          
          return true;                
        }        
      } else {  //unsat                             
        oblig_unsat++;
        
        if (ob->depth == 0) { //"base level conflict"
          assert(conflict_out.size() <= 1); //only possibly the initial marker         
          
          if (conflict_out.size() == 0 || target_layer_out == inductive_layer_idx) {
            printf("// UNSAT: unconditional empty clause derived, ");
            if (conflict_out.size() > 0) {        
              assert(conflict_out[0] == mkLit(2*sigsize));
              printf("in fact a (0,*)-clause.\n");         //for AIGER only in reverse mode        
            } else if (target_layer_out < inductive_layer_idx) {
              printf("in fact a (*,%d)-clause.\n",phase);  //for AIGER only in normal mode
            } else {
              printf("in fact a (*,*)-clause.\n");         //never for AIGER (without environment constraints)
            }
            
            return true;
          }

          //delete obligations pushed to death
          for (OblDeque::iterator it = obligations[phase+1].begin(); it != obligations[phase+1].end(); ++it)
            delete (*it);
          obligations[phase+1].clear();
          
          return false;

        } else { // regular conflict        
          clauses_dersolver++;
          
          // THIS IS THE RESCHEDULING PART (we could even keep them longer, but they should die eventually, shouldn't they?):
          // CAREFUL we do rescheduling even before handling the clause, so that in case of generalization even this pushed ob will get killed
          if (opt_resched) {
            assert(obl_top <= phase);
            obligations[obl_top+1].push_back(ob);           
            oblig_resched_clause++;
          } else 
            delete ob;                   
          
          // convert the conflict to the upper signature and possibly remove the step marker
          int i,j;      
          for (i = 0, j = 0; i < conflict_out.size(); i++) {
            if (var(conflict_out[i]) == 2*sigsize) {
              assert(sign(conflict_out[i]));
              // the step clause marker doesn't go into learned clauses
            } else {
              assert(var(conflict_out[i])<sigsize);
              Lit lit = mkLit(var(conflict_out[i])+sigsize,sign(conflict_out[i]));
              conflict_out[j++] = lit;
            }
          }
          conflict_out.shrink(i-j);          
          conflict_out.push(goal_lit);  // doing it the monotone way!          
          sort(conflict_out);  // sort for fast subsumption checks                         
          
          ABSTRACTION_TYPE abs = calcAbstraction(conflict_out);
          
          if (target_layer_out == inductive_layer_idx) {
            clauses_univ++;
           
            marks_tmp.clear();
            handleNewClause(phase+1,model_idx,0,abs,conflict_out,marks_tmp);
            
            CWBox *clbox = new CWBox(abs,conflict_out);
            clbox->integrate(&layers[phase+1]);           
          } else {
            // TODO: for uniformity's sake, we can have this layer ready as well             
            if (target_layer_out == phase) // there is a possibility of learning a clause that would minimally belong to a layer that doesn't exist yet              
              target_layer_out = phase-1;  // we put it into the previous and a later push will move it further            
            // this is only correct, because the clause in question is in a sense "overgeneralized" - (real obligations, which need to be killed, never sit further than in L_{phase})
                                   
            marks_tmp.clear();
            marks_tmp.push(target_layer_out+1);            
            handleNewClause(target_layer_out+1,model_idx,0,abs,conflict_out,marks_tmp);
            
            CWBox *clbox = new CWBox(abs,conflict_out);
            clbox->integrate(&layers[target_layer_out+1]);
  
            CWBox *prbox = new CWBox();
            prbox->integrate(&push_requests[target_layer_out+1]);
            
            clbox->other = prbox;
            prbox->other = clbox;            
          }                   

          // Experiment temporary - very stupid repetition test:
          for (int i = 1; i < phase; i++)
            if (layers[i] == 0) {
              printf("// UNSAT: repetition detected!\n");
              if (opt_verbose)
                printf("// Delta-layer %d emptied by subsumption!\n",i);            
              return true;              
            }
        }
      }
    }     
  }
   
  void iterativeSearch() {
    assert(initial_obligation.ma.size() == 0);
    initial_obligation.ma.push(mkLit(2*sigsize,  true)); // not (L_initial)                 
    
    layers.push();      // the inducive layer    
    obligations.push(); // those surviving till next phase 
    
    clock_StartCounter(clock_MAIN);
    
    for (phase = 0; ; phase++) {
      layers.push();                             // place for the new layer                  
      if (layers[phase])                          // inductive layer non-empty ?
        layers[phase]->relocate(&layers[phase+1]);  // shift it by one and make the phase-th one empty
      
      assert(layers[phase] == 0);      

      obligations.push();      // the zero-th will be always empty: obligation at index i, has its ma inside L_i
      push_requests.push();
      witnesses.push();
      
      solvers.push(new MarkingSolver());      
      MarkingSolver &solver = *solvers.last();            
      solver.initilazeSignature(2*sigsize+1);      
              
      vec<int> marker; /*empty*/
      
      for (int i = 0; i < rest_clauses.size(); i++)
        solver.addClause(rest_clauses[i],marker);
      
      // insert from univs
      for (CWBox* layer_box = layers[phase+1]; layer_box != 0; layer_box = layer_box->next)           
        solver.addClause(layer_box->data,marker);

      if (phase == 0) {
        marker.push(0); // but 0-th layer will remain empty
        
        // in fact, this is just the single literal single clause
        for (int i = 0; i < goal_clauses.size(); i++)
          solver.addClause(goal_clauses[i],marker);
      }
      
      if (!solver.simplify()) {
        printf("// UNSAT: unconditionally solved by unit propagation!\n");
        return;
      }
           
      if (opt_pphase) {
        printf("\n------------------------------------------------------------------\n");        
        printf("// Starting phase %d...",phase);                
        printf("\n------------------------------------------------------------------\n");        
      } 
      
      if (phase >= opt_startphase) {                                   
        if (processObligations())
          return; // problem solved                 
      }
                  
      if (opt_verbose && opt_pphase) {
        printStat(true);                
      }
      
      if (opt_phaselim && phase >= opt_phaselim) {
        printf("// UNRESOLVED: phase limit reached!\n");
        return;
      }
    }
  }
};

const int SolvingContext::inductive_layer_idx = INT_MAX-1;  
const int SolvingContext::assumption_mark_id  = INT_MAX;

//=================================================================================================

SolvingContext* global_context;

static void prepareClause(vec<Lit>& clause_out, const vec<Lit> &clause_in, int sigsize, bool shifted, Lit litToAdd = lit_Undef) {
  clause_out.clear();
  int shift = shifted ? sigsize : 0;
  
  for (int j=0; j < clause_in.size(); j++) {
    Lit l = clause_in[j];  
    clause_out.push(mkLit(var(l)+shift,sign(l)));
  }
  
  if (litToAdd != lit_Undef)
    clause_out.push(litToAdd);       
}

static void verifyStep(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step, vec<bool>& cur_model, vec<bool>& prev_model, int idx, bool last) { 
  if (!opt_reversed && idx == 0 || opt_reversed && last) { // check initial
    for (int i = 0; i < initial.size(); i++) {
      for (int j = 0; j < initial[i].size(); j++) 
        if (cur_model[var(initial[i][j])] != sign(initial[i][j]))
          goto next_initial_clause;
      
      printf("Initial clause UNSAT: "); printLits(initial[i]);
      assert(false);
            
      next_initial_clause: ;
    }            
  }

  if (!opt_reversed && last || opt_reversed && idx == 0) { // check goal
    for (int i = 0; i < goal.size(); i++) {
      for (int j = 0; j < goal[i].size(); j++) 
        if (cur_model[var(goal[i][j])] != sign(goal[i][j]))
          goto next_goal_clause;
            
      printf("Goal clause UNSAT: "); printLits(goal[i]);
      assert(false);
            
      next_goal_clause: ;
    }            
  }
  
  // check universal
  {
    for (int i = 0; i < universal.size(); i++) {
      for (int j = 0; j < universal[i].size(); j++) 
        if (cur_model[var(universal[i][j])] != sign(universal[i][j]))
          goto next_universal_clause;
            
      printf("Universal clause UNSAT: "); printLits(universal[i]);
      assert(false);
            
      next_universal_clause: ;
    }
  }
  
  // check step
  if (idx > 0) {
    for (int i = 0; i < step.size(); i++) {
      for (int j = 0; j < step[i].size(); j++)
        if (var(step[i][j]) < sigsize) {
          if (!opt_reversed && prev_model[var(step[i][j])] != sign(step[i][j]) || 
               opt_reversed && cur_model[var(step[i][j])] != sign(step[i][j]))
            goto next_step_clause;
        } else {
          if (!opt_reversed && cur_model[var(step[i][j])-sigsize] != sign(step[i][j]) ||
               opt_reversed && prev_model[var(step[i][j])-sigsize] != sign(step[i][j]))
            goto next_step_clause;        
        }
                      
      printf("Step clause UNSAT: "); printLits(step[i]);
      assert(false);
            
      next_step_clause: ;
    }   
  }  
}

static void analyzeSpec(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  SolvingContext& context = *global_context;
  
  Lit goal_lit = lit_Undef;
     
  clock_StartCounter(clock_SIMP);      
        
  int new_sigsize;
  SimpSolver simpSolver;
  vec<Lit> cur_clause;
  
  //TODO: play with these guys -- and with other params if you wish...    
  //simpSolver.use_asymm = true;
  //simpSolver.grow = 10;
  
  // 0,1,...,sigsize-1           the basic signature
  // sigsize,...,2*sigsize-1     the primed signature
  // 2*sigsize                   the initial marker 
  // 2*sigsize+1                 the goal marker
  for (int j = 0; j < 2*sigsize+2; j++)
    simpSolver.newVar();

  // initial clauses
  for (int j = 0; j < initial.size(); j++) {   
    prepareClause(cur_clause,initial[j],sigsize,true,mkLit(2*sigsize));  // marked as initial    
    simpSolver.addClause(cur_clause);
  }
  
  assert(goal.size() == 1);
  assert(goal[0].size() == 1);    
  
  // goal clauses
  for (int j = 0; j < goal.size(); j++) {
    prepareClause(cur_clause,goal[j],sigsize,true,mkLit(2*sigsize+1));   // marked as goal (second literal is needed! otherwise minisat kills the opposite literal when the unit goal is inserted)
    
    goal_lit = goal[0][0];           
    goal_lit = mkLit(var(goal_lit)+sigsize,sign(goal_lit));
    //printf("Goal lit: "); printLit(goal_lit); printf("\n");
    
    simpSolver.addClause(cur_clause);
  }
  assert(goal_lit != lit_Undef);
  
  // universal clauses
  for (int j = 0; j < universal.size(); j++) {    
    prepareClause(cur_clause,universal[j],sigsize,true);  //universals are unmarked
    simpSolver.addClause(cur_clause);
  }
  
  // step clauses    
  for (int j = 0; j < step.size(); j++) {
    prepareClause(cur_clause,step[j],0,false,mkLit(2*sigsize,true));  // marked as incompatible with initial
    simpSolver.addClause(cur_clause);
  }
    
  // freeze the markers, and all variables from lower signature
  simpSolver.setFrozen(2*sigsize,true);
  simpSolver.setFrozen(2*sigsize+1,true);
  simpSolver.setFrozen(var(goal_lit),true);
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
    
    clock_StopPassedTime(clock_SIMP);
    return;
  }
  //printf("eliminated_vars: %d\n",simpSolver.eliminated_vars);
  //printf("sub_subsumed: %d\n",simpSolver.sub_subsumed);
  //printf("sub_deleted_literals: %d\n",simpSolver.sub_deleted_literals);
  //printf("asymm_lits: %d\n",simpSolver.asymm_lits);
  
  Clauses simpClauses;
  simpSolver.copyOutClauses(simpClauses);
    
  vec<Var> renaming;
  vec<Var> inv_renaming;
  
  vec<bool>& bridge_variables = context.bridge_variables;    
  
  for (int i = sigsize; i < 2*sigsize+2; i++) { // the two markers didn't get eliminated!
    renaming.push();
    
    if (!simpSolver.isEliminated(i)) { // the goal_lit goes in as well, that's why ma_subsumption testing works!                 
      renaming.last() = inv_renaming.size();
      inv_renaming.push(i-sigsize);      
      bridge_variables.push(simpSolver.isFrozen(i));
      // printf("%s",simpSolver.isFrozen(i) ? "B" : "*");
    } else {
      renaming.last() = var_Undef;        
      // printf("-");
    }    
  }
  // printf("\n");
  
  new_sigsize = inv_renaming.size() - 2; //the two markers don't count
  context.sigsize = new_sigsize;
  
  if (opt_verbose) {
    printf("// Eliminated %d variables -- new sigsize: %d.\n",simpSolver.eliminated_vars,new_sigsize);
    printf("// Simplified from %d to %d clauses.\n",before,simpSolver.nClauses());          
  }
  
  for (int i = 0; i < simpClauses.size(); i++ ) {
    vec<Lit>& clause = simpClauses[i];

    int j,k;
    bool goal = false;
    
    for (j = 0, k = 0; j < clause.size(); j++) {
      Lit l = clause[j];
      Var v = var(l);

      if (v == 2*sigsize+1) { // we remeber it, but newly don't keep explicitly anymore (will later use MarkingSolver instead)
        assert(!sign(l));
        goal = true;
      } else {
        clause[k++] = l;
      }
    }
    clause.shrink(j-k);  //one literal potentially missing            

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
    
    // printf("%s clause: ",goal ? "Goal" : "Normal"); printLits(clause);
    
    Clauses& target = (goal ? context.goal_clauses : context.rest_clauses);

    int idx = target.size();
    target.push();
    clause.moveTo(target[idx]);            
  }
  
  clock_StopPassedTime(clock_SIMP);
  
  assert(context.goal_clauses.size() == 1);
  assert(context.goal_clauses[0].size() <= 1); // can be empty
  if (context.goal_clauses[0].size() == 1)
    context.goal_lit = context.goal_clauses[0][0];
  else 
    context.goal_lit = lit_Undef;
  
  //printf("Goal lit: "); printLit(context.goal_lit); printf("\n");
  
  context.iterativeSearch();    
  
  Clauses& model_path = context.model_path;
    
  if (model_path.size() > 0                // the SAT CASE
       && (strcmp(opt_format,"dimspec") == 0)
       && opt_print_solution) {   // and somebody is interested             
    
    vec<bool> prev_model;
    vec<bool> cur_model;
    int model_idx = 0;
    
    printf("solution %d %d\n",sigsize - (context.artificial_goal_var ? 1 : 0),model_path.size());
     
    //translate to the original signature and print      
    for (int i = (opt_reversed ? 0 : model_path.size()-1); 
                 (opt_reversed ? i <= model_path.size()-1 : i >= 0);
                 i += (opt_reversed ? 1 : -1)) {
      vec<Lit> &cur_ma = model_path[i];
               
      //clear the model in simpSolver
      simpSolver.model.clear();
      simpSolver.model.growTo(simpSolver.nVars());
      for (int j = 0; j < simpSolver.nVars(); j++)
        simpSolver.model[j] = l_Undef;     
  
      //everything is in lower (except the initial/non-initial markers) -> will go to upper after renaming
      for (int j = 0; j < cur_ma.size(); j++)
        if (var(cur_ma[j]) < new_sigsize) {
          Var v = inv_renaming[var(cur_ma[j])] + sigsize;
          
          simpSolver.model[v] = lbool(!sign(cur_ma[j]));
        }
        
      if (i == model_path.size()-1) //the first model of the sequence - turn on initial
        simpSolver.model[2*sigsize] = l_False;
            
      if (i == 0) //the last model of the sequence - turn on goal
        simpSolver.model[2*sigsize+1] = l_False;      
  
      simpSolver.extendModel();
      bool space = false;
      cur_model.clear();
      for (int j = sigsize; j < 2*sigsize; j++) {
        assert(simpSolver.model[j] != l_Undef);
        
        if (!context.artificial_goal_var || j < 2*sigsize-1) {       
          printf("%s%s%d", (j==sigsize)?"":" ", (simpSolver.model[j]==l_True)?"":"-", j-sigsize+1);
          space = true;
        }
               
        cur_model.push(simpSolver.model[j]==l_True);        
      }
                 
      printf("%s0\n",space?" ":"");                                               
      
      verifyStep(sigsize,initial,goal,universal,step,cur_model,prev_model,model_idx++,(opt_reversed ? i == model_path.size()-1 : i == 0));
      cur_model.copyTo(prev_model);
    }
  }  
}

//=================================================================================================

bool ensure_single_unit_goal(int &sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  if (goal.size() == 1 && goal[0].size() == 1)
    return false;
    
  vec<Lit> cur;

  // uses the original sigsize value thoughout, but in fact one new variable:
  // v_sigsize to have a single clause, single literal goal of the original  
       
  // universals stay untouched + extended old goal clauses are added
  for (int i = 0; i < goal.size(); i++) {
    goal[i].moveTo(cur);
    cur.push(mkLit(sigsize,true)); // ~v_sigsize
    universal.push(cur);
    cur.clear();
  }
  goal.clear();
  
  // just one new goal clause 
  cur.push(mkLit(sigsize,false));  // v_sigsize
  goal.push(cur);
  cur.clear();
  
  //translate the step clauses
  for (int i = 0; i < step.size(); i++) {
    vec<Lit>& clause = step[i];
    for (int j = 0; j < clause.size(); j++)
      if (var(clause[j])>=sigsize)
        clause[j] = mkLit(var(clause[j])+1,sign(clause[j]));
  }

  // enlarge the signature:
  sigsize++;
  printf("// Added 1 variable and 1 clause to represent the goal.\n");  
  return true;
}

static void SIGINT_exit(int signum) {
  printf("// *** INTERRUPTED ***\n");
  if (opt_verbose)
    global_context->printGOStat();
  fflush(stdout);
  _exit(1); 
}

/*
void testCWBox() {
  CWBox* top = 0;
  CWBox* a;
  CWBox* b;
  CWBox* c;
  
  vec<Lit> clause;
  clause.push(mkLit(0));
  
  a = new CWBox(clause);
    
  clause[0] = mkLit(1);
  b = new CWBox(clause);
  
  clause[0] = mkLit(2);
  c = new CWBox(clause);
  
  printf("Integrate c: ");  
  c->integrate(&top);  
  printCWBox(top);
  
  printf("Integrate b: ");  
  b->integrate(&top);  
  printCWBox(top);  
  
  printf("Integrate a: ");  
  a->integrate(&top);  
  printCWBox(top);  
  
  printf("Disintegrate a: ");  
  a->disintegrate();  
  printCWBox(top);  
}
*/

int main(int argc, char** argv)
{
    try {
      setUsageHelp("USAGE: %s [options] <aiger-input-file>\n\n");

#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        // printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif

    //testCWBox();
    //return 0;

    clock_Init();
    clock_StartCounter(clock_OVERALL);

    // THE SPEC:
    int sigsize; 
    Clauses initial;
    Clauses goal;
    Clauses universal;
    Clauses step;
    
    parseOptions(argc, argv, true);
  
    clock_StartCounter(clock_PARSE);

    if (strcmp(opt_format,"aiger") == 0)
      aiger_LoadSpec((argc == 1) ? 0 : argv[1], (int)opt_reversed, (int)opt_pg, /*no parsing chat*/0, opt_kth_property, (int)false,
                   sigsize,initial,goal,universal,step);
    else if (strcmp(opt_format,"dimspec") == 0)
      dimacs_LoadSpec((argc == 1) ? 0 : argv[1], opt_reversed, sigsize, initial, universal, goal, step);
    else {
      printf("Unknown format: %s!\n",(const char *)opt_format);
      exit (1);
    }    
              
    clock_StopPassedTime(clock_PARSE);
    
    if (opt_verbose)
      printf("// Loaded spec -- sigsize: %d, #initial: %d, #goal: %d, #universal: %d, #step: %d\n",sigsize,initial.size(),goal.size(),universal.size(),step.size());

    bool added_new_var = ensure_single_unit_goal(sigsize,initial,goal,universal,step);        
    
    global_context = new SolvingContext();
    global_context->artificial_goal_var = added_new_var;
    
    signal(SIGINT, SIGINT_exit);
    analyzeSpec(sigsize,initial,goal,universal,step);
    
    delete global_context;
    
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("OutOfMemory!\n");
        exit(0);
    }
}

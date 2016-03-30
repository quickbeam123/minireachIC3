/*****************************************************************************************[Main.cc]
Copyright (c) 2013, Martin Suda
Max-Planck-Institut f�r Informatik, Saarbr�cken, Germany
 
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

#include "core/DisjMarkingSolver.h"
#include "core/ClauseSet.h"

#include "simp/SimpSolver.h"
#include "core/Aiger2Spec.h"

#include "core/clock.h"

#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <deque>

#define LOG(X)

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

static BoolOption opt_statpushing("STAT", "spushing", "Print pushing statistics.", true);
static BoolOption opt_statclauses("STAT", "sclauses", "Print layer clause statistics.", true);
static BoolOption opt_statobligations("STAT", "sobligations", "Print model statistics.", true);
static BoolOption opt_statmodel("STAT", "smodel", "Print model statistics.", true);
static BoolOption opt_statlayer("STAT", "slayer", "Print layer statistics.", true);
static BoolOption opt_statreaching("STAT", "sreach", "Print statistics about reaching.", true);

static BoolOption opt_sminim("STAT", "sminim", "Print clause minimization statistics.", true);
static BoolOption opt_sttime("STAT", "stime", "Print time statistics.", true);

static IntOption opt_startphase("MAIN", "startphase", "Initial phase to start with (may become incomplete for non-monot designs).", 0, IntRange(0,INT32_MAX));

static BoolOption opt_minimize ("MAIN", "min", "(Inductively) minimize learned clauses.", true); 
static IntOption opt_induction ("MAIN", "ind", "Use induction for minimization (1 = one pass, 2 = iterate until fixpoint).", 2, IntRange(0,2)); 

static BoolOption opt_print_solution ("MAIN", "psol", "Print the solution assignment (for dimspec format inputs).", false);
static BoolOption opt_move_auxil ("MAIN", "aux", "Move low auxiliary variables to upper signature.", true);

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

static int ids = 0;

/* wrapper for layer clauses and their witness */
struct CWBox {
  int id;

  vec<Lit> data;         // for clause the actual literals, for witness the negated state as a clause
  ABSTRACTION_TYPE abs;  // abstraction of the above
  
  CWBox*  other;  // the other of the two; the other is 0 for a clause iff it is a BAD lemma
  
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

struct Oblig {
  bool alive;
  CWBox* from_clause; // a push reques associated with a clause, or 0 if the this is a must obligation

  vec<Lit> ma;
  ABSTRACTION_TYPE abs; // abstraction of the above
  
  Oblig() : alive(false), from_clause(0) {}
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

struct SolvingContext {
  Lit goal_lit;
  int sigsize;

  Clauses goal_clauses;
  Clauses rest_clauses;
  
  Clauses reaching_states; // discovered states which reach the goal (to be disjioned with the goal formula)
  
  vec<bool> bridge_variables; 
  // TODO: this idea should be extended up to the point where the low signature part of the solver is only as big as the bridge (the rest of the variables are just rubbish!)
  // Well, in general this is a little more complicated: remember there is S_in, S_out, and S_reg in the  Niklases' paper -- the low signature should contain S_in and S_reg

  int phase;
  
  vec<DisjunctionMaintainingMarkingSolver*> solvers;
  
  CBoxVec layers;         // here sit the clauses   
  CBoxVec push_requests;  // to easily find the non-bad ones in a particular layer (this could be done differently and more sensibly)
   
  vec<Oblig> obligations; // there is no rescheduling, so we just need a stack of as many Oblig's as the current phase
        
  // statistics
  int pushing_request;
  int pushing_success;

  int oblig_must_injected;
  int oblig_may_injected;
  int oblig_processed;
  int oblig_subsumed;
  int oblig_sat_may;
  int oblig_sat_must;
  int oblig_hit_reaching;
  int oblig_unsat;
  
  int reaching_found;
  
  int clauses_dersolver;
  int clauses_univ;
  int clauses_subsumed;
  int clauses_found_bad;
  
  int solver_call_extension;
  int solver_call_push;
  
  int minim_attempts;  
  int minim_solver;
  int minim_explicit;
  int minim_push;
  
  SolvingContext() : phase(-1),
                     pushing_request(0), pushing_success(0),
                     oblig_must_injected(0), oblig_may_injected(0), oblig_processed(0), oblig_subsumed(0), oblig_sat_may(0), oblig_sat_must(0), oblig_hit_reaching(0), oblig_unsat(0),
                     reaching_found(0),
                     clauses_dersolver(0), clauses_univ(0), clauses_subsumed(0), clauses_found_bad(0),
                     solver_call_extension(0), solver_call_push(0),                     
                     minim_attempts(0), minim_solver(0), minim_explicit(0), minim_push(0)
      {}

  void deleteClause(CWBox *cl_box) {
    if (cl_box->other) {
      if (cl_box->other->prev) // was still integrated
        cl_box->other->disintegrate();
      delete cl_box->other;
    }
    cl_box->disintegrate();
    delete cl_box;
  }
  
  ~SolvingContext() {
    if (opt_verbose)
      printGOStat();      
    
    for (int i = 0; i < layers.size(); i++)
      while (layers[i])
        deleteClause(layers[i]);

    for (int i = 0; i < solvers.size(); i++)
      delete solvers[i];     
  }
  
  void printStat() {
    if (opt_statpushing) {
      printf("\nClause pushing:\n");                     
      printf("\t%d requests handled.\n",pushing_request);
      printf("\t%d clauses pushed.\n",pushing_success);
    
      pushing_request = 0;
      pushing_success = 0;      
    }
       
    if (opt_statobligations) {
      printf("\nObligations:\n");
      printf("\t%d must-injected,\n",oblig_must_injected);
      printf("\t%d may-injected,\n",oblig_may_injected);
      printf("\t%d processed,\n",oblig_processed);
      printf("\t%d may extended,\n",oblig_sat_may);
      printf("\t%d must extended,\n",oblig_sat_must);
      printf("\t%d hit reaching,\n",oblig_hit_reaching);
      printf("\t%d blocked,\n",oblig_unsat);    
      printf("\t%d subsumed,\n",oblig_subsumed);
      
      oblig_must_injected = 0;
      oblig_may_injected = 0;
      oblig_processed = 0;
      oblig_subsumed = 0;            
      oblig_sat_may = 0;
      oblig_sat_must = 0;
      oblig_hit_reaching = 0;
      oblig_unsat = 0;
    }  
  
    if (opt_statreaching) {
      printf("\nReaching states:\n");
      printf("\t%d found,\n",reaching_states.size() - reaching_found);
      printf("\t%d in total.\n",reaching_states.size());
      
      reaching_found = reaching_states.size();
    }
  
    if (opt_statclauses) {
      printf("\nClauses:\n");
      printf("\t%d derived by solver (%d universals), subsumed %d.\n",clauses_dersolver,clauses_univ,clauses_subsumed);
      printf("\t%d found bad,\n",clauses_found_bad);
      
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
      clauses_subsumed = 0;
      clauses_found_bad = 0;
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
     
   
  bool callSolver(int index, CLOCK_CLOCKS cc,       // calls the index-th solver, under then give assumptions filtered_ma plus the layer assumptions
                  bool compute_conflict,          // request for returning (minimized, if flag set) appropriate conflict clause (to be delivered in conflict_out), 
                                                  // also, target_layer_out will containt index of the least delta layer on which the conflict depends (or inductive_layer_idx for "infty")
                  bool induction) {               // allow using induction during minimization
                                                           

    DisjunctionMaintainingMarkingSolver& solver = *solvers[index];

    LOG(printf("Calling for solver %d with ma ",index); printLits(filtered_ma);)
                 
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
            break; // TODO: this is where we could already take a good witness (would save one call)
          
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
        LOG(printf("subsumed clause %d\n",tmp_box->id);)
        deleteClause(tmp_box);
        res++;
      } else if (testForWeak && absSubsumes(layer_box->abs,abs) && subsumes(layer_box->data,clause)) {
        LOG(printf("subsumed by %d\n",layer_box->id);)
        assert(res == 0);        
        return -1;
      } else {
        layer_box = layer_box->next;
      }
    }
                
    return res;
  }
     
  
  /* 
    A new strong clause is coming to this layer, so it could initiate some pushing by killing a witness.
  */
  /*
  int pruneWitnesses(ABSTRACTION_TYPE abs,
                     vec<Lit>const & clause,   //the potentially subsuming clause
                     int from) {  
    if (from > phase)
      return 0;
    
    int res = 0;
    
    for(CWBox* wit_box = witnesses[from]; wit_box != 0; ) { //iteration inside
      // to make subsumptions by layer clauses work, we need to store goal_lit with all ma's and witnesses
    
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
  */
  
    /* 
    A new strong clause is coming to this layer, maybe some obligations will be pushed back.
    (not killed, actually, they all wait for the phase to be over, since they could be somebody's parents)
  */
  /*
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
    
      // to make subsumptions by layer clauses work, we need to store goal_lit with all ma's and witnesses
      
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
  }*/
  
  /*
    a new clause (either just derived or pushed) is coming to this layer
  */
  void handleNewClause(int target_layer, int first_questionable, int upmost_layer, ABSTRACTION_TYPE abs, vec<Lit> const & clause, vec<int> const& markers) {
    //printf("Inserting %s-clause to layer %d to kill ma in layer %d. ",target_layer <= phase ? "N" : "U",target_layer,first_questionable+1);
           
    for (int i = target_layer; i >= upmost_layer; i--) {
      int res = pruneLayerByClause(abs,clause,i,/* maybe_weak (?)*/ i <= first_questionable /* otherwise don't test forward */ );
                                  
      if (res < 0) { //got subsumed here; will not subsume anymore
        assert(i < target_layer);                 // got inserted into his target layer
        assert(i <= first_questionable);          // should be strong even up to this point
        // printf("Killed in %d. ",i);                   
        
        return;
      } else {
        clauses_subsumed += res;

        Oblig& ob = obligations[i];
        if (ob.alive && absSubsumes(abs,ob.abs) && subsumes(clause,ob.ma)) {
          ob.alive = false;
          oblig_subsumed ++;
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
    new clause, push clause, or a clause with a killed witness is looking for a new one
  */
  /*
  void lookForWitness(CWBox * cl_box, int index) {
      }
  */
  
  /*
  bool doSomePushing(int upto) {  
    // NOTE: don't call with ( upto > phase ) before the phase is over, otherwise the unsat claim doesn't hold     
    for (int i = least_affected_layer; i < upto; i++) {
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
      
      least_affected_layer = upto;
    }
      
    return false;
  }
  */
  
  // the positive part of extending is shared for both injection and proper extension
  // the negative done differently by each caller, assuming call to the solver returned false
  bool extend(int model_idx, Oblig& ob_from, Oblig& ob_to, bool induct, bool& solved) {
    solved = false;
  
    vec<Lit> &our_ma = ob_from.ma;

    oblig_processed++;
    solver_call_extension++;
  
    filtered_ma.clear();
    for (int i = 0; i < our_ma.size(); i++) {
      assert(var(our_ma[i]) >= sigsize);
      if (var(our_ma[i]) < 2*sigsize) { 
        // if (bridge_variables[var(our_ma[i])-sigsize]) - we do the filtering when storing the ma already
          filtered_ma.push(mkLit(var(our_ma[i])-sigsize,!sign(our_ma[i])));
      } else if (our_ma[i] != goal_lit) { // goal lit could be there to make subsumption work
        filtered_ma.push(our_ma[i]);      // this is the initial / step marker
      }
    }
      
    if (callSolver(model_idx,clock_SOLVER_EXTEND,true,induct)) {
      
      DisjunctionMaintainingMarkingSolver &model_solver = *solvers[model_idx];
      
      if (model_idx == 0 || model_solver.value(goal_lit) == l_True) {
        if (ob_from.from_clause) { // a may obligation
          LOG(printf("Reaching states found\n");)
        
          if (model_idx)
            oblig_hit_reaching++;
        
          // if there is a clause, it is now bad
          CWBox* req_box = ob_from.from_clause;
          
          // if there is a clause, it is now bad
          CWBox* cl_box = req_box->other;
          if (cl_box) {
            cl_box->other = 0;
            req_box->other = 0;
            
            clauses_found_bad++;
          } else {
            assert(req_box->other == 0);
          }
          
          int new_reaching_start = reaching_states.size();
          int idx = model_idx+1;
          assert(&ob_from == &obligations[idx]);
          while (idx <= phase /* actually, there should never be a may-obligation at index "phase", at least not as we currently do things */
                && obligations[idx].from_clause == req_box) {
            Oblig& ob = obligations[idx];
            vec<Lit>& our_ma = ob.ma;
          
            // 1) the state is becoming reaching
            reaching_states.push();
            vec<Lit>& state = reaching_states.last();
            
            for (int i = 0; i < our_ma.size(); i++) {
              assert(var(our_ma[i]) >= sigsize);
              if (var(our_ma[i]) < 2*sigsize) { // staying up, but negated -> in a state form
                state.push(mkLit(var(our_ma[i]),!sign(our_ma[i])));
              }
              // ignoring goal_lit and the step marker
            }
            
            LOG(printf("At %d: ",idx); printLits(state);)
            
            // 2) no longer alive
            ob.alive = false;
          
            idx++;
          }
          
          // insert new reaching states into solvers
          for (int i = 0; i < solvers.size(); i++)
            for (int j = new_reaching_start; j < reaching_states.size(); j++)
              solvers[i]->disjoinWithUnits(reaching_states[j]);
          
          // req_box dies
          assert(!req_box->prev);
          // req_box->disintegrate(); // should have been disintegrated when this may-chain started
          delete req_box;
          
          return true;
          
        } else { // a must obligation
        
          printf("// SAT: model found at index %d\n",model_idx);
          solved = true;
          return true;
        }
      }
      
      if (ob_from.from_clause) {
        LOG(printf("Sucessful extenstion of a may obligation.\n");)
        oblig_sat_may++;
      } else {
        LOG(printf("Sucessful extenstion of a must obligation.\n");)
        oblig_sat_must++;
      }
      
      ob_to.alive = true;
      ob_to.from_clause = ob_from.from_clause;
      
      vec<Lit>& ma = ob_to.ma;
      ma.clear();
      for (int j = 0; j < sigsize; j++) {
        assert(model_solver.model[j+sigsize] != l_Undef);
        if (bridge_variables[j]) // careful, the bridgevar trick is not to be compatible with model for printing
          ma.push(mkLit(j+sigsize,model_solver.model[j+sigsize] == l_True)); // the literals are negated ("stored in a clause form")
      }
      // only after the previous, so that it is sorted
      ma.push(mkLit(2*sigsize, false)); // L_initial assumed true => turning on step clauses, turning off initial clauses
      ma.push(goal_lit); // to make subsumption by layer clauses work
      ob_to.abs = calcAbstraction(ma);
    
      return true;
    }
    return false;
  }
  
  Oblig initial_obligation;
  
  bool processObligations() {
    int top = 0;
  
    LOG(printf("processObligations - start; phase %d, top %d\n",phase, top);)
  
    while (top <= phase) {
      LOG(printf("processObligations - loop; top %d\n",top);)
    
      if (obligations[top].alive) { // will be extending
        LOG(printf("processObligations - extending\n");)
      
        assert(top > 0);
        
        bool solved;
        
        if (!extend(top-1,obligations[top],obligations[top-1],true,solved)) { // new concflict clause derived
          oblig_unsat++;
          clauses_dersolver++; // TODO: do we need both?
          
          // TODO: make sure you prune obligations all the way it's necessary!
          
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
            
            LOG(printf("Failed extension; derived a universal clause: "); printClause(conflict_out,marks_tmp);)
            
            handleNewClause(phase+1,top-1,0,abs,conflict_out,marks_tmp);
            
            CWBox *clbox = new CWBox(abs,conflict_out);
            clbox->integrate(&layers[phase+1]);           
          } else {
            // TODO: for uniformity's sake, we can have this layer ready as well             
            if (target_layer_out == phase) // there is a possibility of learning a clause that would minimally belong to a layer that doesn't exist yet              
              target_layer_out = phase-1;  // we put it into the previous and a later push will move it further            
            // this is only correct, because the clause in question is in a sense "overgeneralized" - (real obligations, which need to be killed, never sit further than in L_{phase})
                                   
            marks_tmp.clear();
            marks_tmp.push(target_layer_out+1);
            
            LOG(printf("Failed extension; derived a layer clause to layer %d: ",target_layer_out+1); printClause(conflict_out,marks_tmp);)
            
            handleNewClause(target_layer_out+1,top-1,0,abs,conflict_out,marks_tmp);
            
            CWBox *clbox = new CWBox(abs,conflict_out);
            clbox->integrate(&layers[target_layer_out+1]);
  
            CWBox *prbox = new CWBox();
            prbox->integrate(&push_requests[target_layer_out+1]);
            
            clbox->other = prbox;
            prbox->other = clbox;            
          }
          
          // top stays the same; in the standard, non-over-generalized case, the new clause has now it's push request in push_requests[top] which should be handled next
          
        } else {
          // successful extension:
          if (solved)
            return true;
        
          top--; // one step forward
        }
        
        continue;
      }
      
      if (top == phase) { // will be injecting obligation into obligations[phase]
        LOG(printf("processObligations - injecting\n");)
      
        bool solved;
      
        if (!extend(phase,initial_obligation,obligations[top],false /* induction is not correct for the initial call */,solved)) {
        
          LOG(printf("failed injection -- end of phase\n");)
        
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
          
          return false;
        }
        
        LOG(printf("Injected to %d\n",phase);)
        
        oblig_must_injected++;
        
        if (solved) // injected directly to the goal
          return true;
        
        // succesful injection; top stays
      
        continue;
      }
      
      if (push_requests[top]) { // do some pushing -- TODO: later try optimizing the order in which clauses are pushed!
        LOG(printf("processObligations - pushing\n");)
      
        assert(top > 0);
      
        CWBox* req_box = push_requests[top];
        CWBox* cl_box = req_box->other;
        
        if (!cl_box) { // dead clause has left a push request
          req_box->disintegrate();
          delete req_box; // by now there is no alive may obligation pointing to this req_box!
          continue;
        }
        
        vec<Lit> & clause = cl_box->data;
        solver_call_push++;
        pushing_request++;
              
        filtered_ma.clear();
        for (int l = 0; l < clause.size(); l++) {
          assert(var(clause[l]) >= sigsize);
          if (clause[l] != goal_lit)
            filtered_ma.push(mkLit(var(clause[l])-sigsize,!sign(clause[l])));
        }
        filtered_ma.push(mkLit(2*sigsize, false));

        if (callSolver(top,clock_SOLVER_PUSH,false,false)) {
          // TODO: Could this be made inductive and merged with other extensions? (kind of a push request injection, right?)
          // Are we afraid of partial models? We know how to do ternary (though only in rev, without pg and without simp) which uses partial all the time!
          
          oblig_may_injected++;
          
          DisjunctionMaintainingMarkingSolver &model_solver = *solvers[top];
          
          if (model_solver.value(goal_lit) == l_True) {
            clauses_found_bad++;
          
            LOG(printf("Pushing failed, jumped to reachable at %d -- clause is bad\n",top);)
          
            // hit a goal-reaching state in layer[top] while it's predecessor satisfies non C => C is bad, never push again!
            cl_box->other = 0;
            req_box->disintegrate();
            delete req_box;
            
            // TODO: here we could also try extracting the reaching state from the predecessor, but let's say we will systematically not do it (for now)
            // (we never extract states from the lower signature)
            
          } else {
          
            LOG(printf("Pushing failed, may obligation injected to %d\n",top);)
          
            Oblig& ob = obligations[top];
            ob.alive = true;
            ob.from_clause = req_box; // starting a new may-chain
            
            req_box->disintegrate(); // this means we only inject once (per phase)
            req_box->prev = 0; // unintegrated !
            
            // extract the witness
            vec<Lit> & ma = ob.ma;
            ma.clear();

            for (int j = 0; j < sigsize; j++) {
              assert(model_solver.model[j+sigsize] != l_Undef);  
              if (bridge_variables[j]) // does a reaching state need to be fully specified?
                ma.push(mkLit(j+sigsize,model_solver.model[j+sigsize] == l_True));  //but it stays in upper signature and negated ("as a clause")
            }
            // only after the previous, so that it is sorted
            ma.push(mkLit(2*sigsize, false)); // L_initial assumed true => turning on step clauses, turning off initial clauses
            ma.push(goal_lit); // to make subsumption by layer clauses work
            ob.abs = calcAbstraction(ma);
            
            // push_request stays in push_requests[top]; ob will be the thing to work on next, in the next iteration
          }
        } else {     // pushed
          marks_tmp.clear();
          marks_tmp.push(top+1);
        
          pushing_success++;
        
          LOG(printf("Pushing success, moving clause to layer %d\n",top+1);)
        
          handleNewClause(top+1,top /* it should not get subsumed there */,top+1,cl_box->abs,clause,marks_tmp);
        
          cl_box->disintegrate();
          cl_box->integrate(&layers[top+1]);
          
          req_box->disintegrate();
          req_box->integrate(&push_requests[top+1]);
          
          if (layers[top] == 0) {
            printf("// UNSAT: repetition detected!\n");
            if (opt_verbose)
              printf("// Delta-layer %d emptied by pushing!\n",top);
            return true;
          }
          
          // check top again, there could be other pushable clauses
        }
        
        continue;
      }
      
      LOG(printf("Nothing to do at index %d\n",top);)
      
      top++;
    }
    return false;
  }
   
  void iterativeSearch() {
    assert(initial_obligation.ma.size() == 0);
    assert(initial_obligation.from_clause == 0); // injector is a must obligation
    initial_obligation.ma.push(mkLit(2*sigsize,  true)); // not (L_initial)
    
    layers.push();      // for the inducive layer
    
    clock_StartCounter(clock_MAIN);
    
    for (phase = 0; ; phase++) {
      layers.push();                                // place for the new layer                  
      if (layers[phase])                            // inductive layer non-empty ?
        layers[phase]->relocate(&layers[phase+1]);  // shift it by one and make the phase-th one empty
      
      assert(layers[phase] == 0);

      obligations.push();      // the zero-th will be always empty: obligation at index i, has its ma inside L_i
      push_requests.push();
      
      solvers.push(new DisjunctionMaintainingMarkingSolver());      
      DisjunctionMaintainingMarkingSolver &solver = *solvers.last();            
      goal_lit = solver.initilazeSignature(2*sigsize+1);
      
      assert(var(goal_lit)>2*sigsize); // in fact, it is the next available var, but we don't need that
      
      // univesally define what the goal_lit stands for:
      solver.disjoinWithCNF(goal_clauses);
      
      for (int i = 0; i < reaching_states.size(); i++) {
        solver.disjoinWithUnits(reaching_states[i]);
      }
      
      vec<int> marker; /*empty*/
      
      for (int i = 0; i < rest_clauses.size(); i++)
        solver.addClause(rest_clauses[i],marker);
      
      // insert from the inductive layer
      for (CWBox* layer_box = layers[phase+1]; layer_box != 0; layer_box = layer_box->next)           
        solver.addClause(layer_box->data,marker);           

      if (phase == 0) {
        marker.push(0); // but 0-th layer will remain empty
        
        // the single literal single goal clause
        vec<Lit> the_goal_clause;
        the_goal_clause.push(goal_lit);
        
        CWBox *clbox = new CWBox(calcAbstraction(the_goal_clause),the_goal_clause);
        clbox->integrate(&layers[0]);
  
        // the_goal_clause is non pushable (no push_request for it) => other remains 0
        // effectively "bad" from the start
        
        solver.addClause(the_goal_clause,marker);
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
      
      // To start a phase by pushing, all we need to do is to put the push_requests of non-bad clauses back
      for (int i = 1; i < phase-1; i++) {
        LOG(printf("Resurrecting requests for %i.\n",i);)
        for (CWBox* layer_box = layers[i]; layer_box != 0;layer_box = layer_box->next) {
          if (layer_box->other)
            layer_box->other->integrate(&push_requests[i]);
        }
      }
        
      if (phase >= opt_startphase) {           
        if (processObligations())
          return; // problem solved
      }
       
      if (opt_verbose && opt_pphase) {
        printStat();
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

/*
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
*/

static void analyzeSpec(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  SolvingContext& context = *global_context;
  
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
  
  // goal clauses
  for (int j = 0; j < goal.size(); j++) {
    prepareClause(cur_clause,goal[j],sigsize,true,mkLit(2*sigsize+1));   // marked as goal (second literal is needed! otherwise minisat kills the opposite literal when the unit goal is inserted)
    simpSolver.addClause(cur_clause);
  }
  
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
    
    if (!simpSolver.isEliminated(i)) {
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

      if (v == 2*sigsize+1) { // we remeber it, but newly don't keep explicitly anymore (will later use DisjunctionMaintainingMarkingSolver instead)
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
  
  context.iterativeSearch();    
  
  /*
  Clauses& model_path = context.model_path;
    
  if (model_path.size() > 0                // the SAT CASE
       && (strcmp(opt_format,"dimspec") == 0)
       && opt_print_solution) {   // and somebody is interested             
    
    vec<bool> prev_model;
    vec<bool> cur_model;
    int model_idx = 0;
    
    printf("solution %d %d\n",sigsize,model_path.size());
     
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
        
        // if (!context.artificial_goal_var || j < 2*sigsize-1) {
          printf("%s%s%d", (j==sigsize)?"":" ", (simpSolver.model[j]==l_True)?"":"-", j-sigsize+1);
          space = true;
        // }
               
        cur_model.push(simpSolver.model[j]==l_True);        
      }
                 
      printf("%s0\n",space?" ":"");                                               
      
      verifyStep(sigsize,initial,goal,universal,step,cur_model,prev_model,model_idx++,(opt_reversed ? i == model_path.size()-1 : i == 0));
      cur_model.copyTo(prev_model);
    }
  }  
  */
}

//=================================================================================================

void auxiliary_variables_to_upper(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  vec<bool> low_auxil(sigsize,true); // all start as low auxil candidates

  for (int i = 0; i < initial.size(); i++) {
    vec<Lit> const & cl = initial[i];
    for (int j = 0; j < cl.size(); j++)
      low_auxil[var(cl[j])] = false;
  }
   
  for (int i = 0; i < goal.size(); i++) {
    vec<Lit> const & cl = goal[i];
    for (int j = 0; j < cl.size(); j++)
      low_auxil[var(cl[j])] = false;
  }
  
  for (int i = 0; i < universal.size(); i++) {
    vec<Lit> const & cl = universal[i];
    for (int j = 0; j < cl.size(); j++)
      low_auxil[var(cl[j])] = false;
  } 

  for (int i = 0; i < step.size(); i++) {
    vec<Lit> const & cl = step[i];
    for (int j = 0; j < cl.size(); j++)
      if (var(cl[j]) >= sigsize)        
        low_auxil[var(cl[j])-sigsize] = false;
  } 
  
  int low_auxil_cnt = 0;
  for (int i = 0; i<sigsize; i++)
    if (low_auxil[i])
      low_auxil_cnt++;
  
  printf("// Detected and moved %d low auxiliary variables\n",low_auxil_cnt);
  
  if (low_auxil_cnt > 0) { // update the encoding
    for (int i = 0; i < step.size(); i++) {
      vec<Lit>& cl = step[i];
      for (int j = 0; j < cl.size(); j++)
        if (var(cl[j]) < sigsize && low_auxil[var(cl[j])])
          cl[j] = mkLit(var(cl[j])+sigsize,sign(cl[j]));
    }  
  }  
}

static void SIGINT_exit(int signum) {
  printf("// *** INTERRUPTED ***\n");
  if (opt_verbose)
    global_context->printGOStat();
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

    if (opt_move_auxil)
      auxiliary_variables_to_upper(sigsize,initial,goal,universal,step);     
        
    global_context = new SolvingContext();
    
    signal(SIGINT, SIGINT_exit);
    analyzeSpec(sigsize,initial,goal,universal,step);
    
    delete global_context;
    
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("OutOfMemory!\n");
        exit(0);
    }
}

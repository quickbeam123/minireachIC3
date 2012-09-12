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

#include "core/MarkingSolver.h"
#include "core/ClauseSet.h"

#include "simp/SimpSolver.h"
#include "core/Aiger2Spec.h"

#include "core/clock.h"

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

static IntOption opt_phaselim ("MAIN", "phaselim", "Terminate after a given number of phases.", 0, IntRange(0,INT32_MAX));

// TODO: This could only make sense under some in-phase clause pushing scenario
static BoolOption opt_earlycheck ("MAIN", "early", "Test for layer repetition each time new clauses enter a layer.", false); 
static BoolOption opt_masubs("MAIN", "masubs", "Test model assumptions for subsumption by layers/univs before actually passing them on to solver.", true);

static IntOption opt_resched ("MAIN", "resched", "Reschedule obligations (allows long models).", 1, IntRange(0,3));

static BoolOption opt_statclauses("STAT", "sclauses", "Print layer clause statistics.", true);
static BoolOption opt_statobligations("STAT", "sobligations", "Print model statistics.", true);
static BoolOption opt_statmodel("STAT", "smodel", "Print model statistics.", true);
static BoolOption opt_statlayer("STAT", "slayer", "Print layer statistics.", true);
static BoolOption opt_sminim("STAT", "sminim", "Print clause minimization statistics.", true);
static BoolOption opt_sttime("STAT", "stime", "Print time statistics.", true);

static IntOption opt_startphase("MAIN", "startphase", "Initial phase to start with (may become incomplete for non-monot designs).", 0, IntRange(0,INT32_MAX));

static BoolOption opt_minimize  ("MAIN", "min", "(Inductively) minimize learned clauses.", true); 
static BoolOption opt_induction ("MAIN", "ind", "Use induction for minimization.", false); 

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
          
    return (lhs->depth > rhs->depth);   // This is rather arbitrary:
    /*
    The opposite version favours deep couterexamples and indeed seems to be slightly better on SAT instances.
    This one, on the other hand, goes forward with the shallow obligations first (i.e. prefers to do first what resched=0 does)
    and seems to be slightly better on unsat (esp in rev).
    */
  }
};

struct SolvingContext {
  Lit goal_lit;
  int sigsize;

  Clauses goal_clauses;
  Clauses rest_clauses;
  
  vec<bool> bridge_variables; 
  // TODO: this idea should be extended up to the point where the low signature part of the solver is only as big as the bridge (the rest of the variables are just rubbish!)
  // Well, in general this is a little more complicated: remember there is S_in, S_out, and S_reg in the  Niklases' paper -- the low signature should contain S_in and S_reg

  vec<MarkingSolver*> solvers;
  vec<JustClauseSet*> layers;   
    
  int phase;
  int least_affected_layer;  
  
  // statistics   
  int clauses_dersolver;
  int clauses_univ;
  int clauses_pushed;
  int clauses_strengthened;
  int clauses_pushsubsumed;
  
  int oblig_processed;
  int oblig_subsumed;
  int oblig_sat;
  int oblig_unsat;
  
  int minim_attempts;  
  int minim_solver;
  int minim_explicit;
  int minim_iductively;
  int minim_push;
    
  int model_min_layer;
  int model_max_depth;  

  // obligation pool
  
  Obligation *pool;
  int poolsize;  
  
  Obligation* acquireObligation() {
    Obligation* res;
    if (pool) {
      res = pool;
      // res->id = ids++;
      pool = pool->next;            
    } else {
      poolsize++;
      res = new Obligation(ids++);      
    }

    return res;
  }
  
  void releaseObligation(Obligation* ob) {
    ob->next = pool;
    pool = ob;
  }
  
  std::priority_queue<Obligation*,std::vector<Obligation*>,ObligationCmp> obligations;  
     
  SolvingContext() : phase(-1),    
                     least_affected_layer(0),
                     clauses_dersolver(0), clauses_univ(0), clauses_pushed(0), clauses_strengthened(0), clauses_pushsubsumed(0),
                     oblig_processed(0), oblig_subsumed(0), oblig_sat(0), oblig_unsat(0),
                     minim_attempts(0), minim_solver(0), minim_explicit(0), minim_iductively(0), minim_push(0),
                     model_min_layer(0), model_max_depth(0),  
                     pool(0), poolsize(0),
                     called(0)
  { }    

  ~SolvingContext() {
    if (opt_verbose)
      printGOStat();      

    for (int i = 0; i < solvers.size(); i++)
      delete solvers[i];
      
    for (int i = 0; i < layers.size(); i++)
      delete layers[i];

    while (!obligations.empty()) {      
      delete obligations.top();
      obligations.pop();
    }

    while (pool) {
      Obligation* next = pool->next;      
      delete pool;
      pool = next;    
    }       
  }
  
  void printStatExtending(bool between_phases = false) {
    if (opt_statclauses) {
      printf("\nClauses:\n");
      printf("\t%d derived by solver (%d universals), subsumed %d.\n",clauses_dersolver,clauses_univ,clauses_strengthened);
      
      int inlayers = 0;
      int length_max = 0;
      int length_sum = 0;
           
      for (int i = 1; i <= phase+1; i++)
        for (JustClauseSet::Iterator it = layers[i]->getIterator(); it.isValid(); it.next()) {
          vec<Lit> const & clause = it.getClause();
                             
          if (clause.size() > length_max)
            length_max = clause.size();            
          length_sum += clause.size();
          inlayers += 1;                
        }           

      printf("\tKept: %d ",inlayers);
      printf("(max %d lits, %f lits on average).\n",length_max, (1.0*length_sum)/inlayers);

      clauses_dersolver = 0;
      clauses_univ = 0;  
      clauses_strengthened = 0;      
    }    
    
    if (opt_statobligations) {
      printf("\nObligations:\n");
      printf("\t%d processed,\n",oblig_processed);
      printf("\t%d subsumed,\n",oblig_subsumed);           
      printf("\t%d extended,\n",oblig_sat);
      printf("\t%d blocked.\n",oblig_unsat);    

      //printf("   maoccursz: %zu\n",mas.size());
      
      oblig_processed = 0;
      oblig_subsumed = 0;      
      oblig_sat = 0;
      oblig_unsat = 0;
    }
    
    if (opt_minimize && opt_sminim) {
      printf("\nMinimzation averages from %d attempts:\n", minim_attempts);
      printf("\t%f by solver,\n",(1.0*minim_solver)/minim_attempts);      
      printf("\t%f by picking (%f from inducive passes),\n",(1.0*minim_explicit)/minim_attempts,(1.0*minim_iductively)/minim_attempts);
      printf("\t%f by pushing.\n",(1.0*minim_push)/minim_attempts);
            
      minim_attempts = 0;
      minim_solver = 0;      
      minim_explicit = 0;
      minim_iductively = 0;
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
      for (int i = 0; i <= phase+1; i++)        
        printf("%d%s%s",layers[i]->size(),(i == phase+1) ? "]" : "|",(i == phase) ? "[" : "");
      printf("\n");
    }      
  }
  
  void printStatPushing(bool between_phases = false) {
    if (opt_statclauses) {
      printf("\nClause pushing:\n");
      printf("\t%d pushed, %d subsumed.\n",clauses_pushed,clauses_pushsubsumed);
    
      clauses_pushed = 0;       
      clauses_pushsubsumed = 0;
    }    
          
    if (opt_statlayer && between_phases) {
      printf("\nLayers: ");
      for (int i = 0; i <= phase+1; i++)        
        printf("%d%s%s",layers[i]->size(),(i == phase+1) ? "]" : "|",(i == phase) ? "[" : "");
      printf("\n");
    }    
  
    if (opt_sttime) {
      clock_StopAddPassedTime(clock_MAIN);
    
      printf("\nTime:\n");
      printf("\tspent in solver extending %fsec\n",clock_GetAkku(clock_SOLVER_EXTEND));
      printf("\tspent in solver pushing   %fsec\n",clock_GetAkku(clock_SOLVER_PUSH));
      printf("\tspent in main   %fsec.\n",clock_GetAkku(clock_MAIN));
      
      clock_InitCounter(clock_MAIN);
      clock_StartCounter(clock_MAIN);
      clock_InitCounter(clock_SOLVER_EXTEND);
      clock_InitCounter(clock_SOLVER_PUSH);
    }  
  }
  
  void printGOStat() {
    printf("// Game over during phase: %d.\n",phase);   
           
    if (phase >= 0)
      printStatExtending();
      
    if (phase >= 0)
      printStatPushing();
     
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
  
  vec<Lit> tmp_ma;
  
  bool maSubsumedInLayer(vec<Lit> &ma, int idx) {          
    tmp_ma.clear();
    tmp_ma.growTo(ma.size());    
    for (int i = 0; i < ma.size(); i++)
      if (var(ma[i]) < sigsize)
        tmp_ma[i] = mkLit(var(ma[i])+sigsize,!sign(ma[i]));
      else {
        assert(var(ma[i]) == 2*sigsize);
        tmp_ma[i] = ~ma[i];
      }
      
    assert(clause_sorted(tmp_ma));

    // note that as we store the goal_lit in all clauses in layers,
    // this subsumption check only ever works because goal_lit is part of the bridge
    // (and all the generated ma's don't satisfy the goal -- otherwise we would terminate with SAT)
    
    for ( ; idx <= phase+1; idx++)
      if (layers[idx]->isSubsumed(tmp_ma))        
        return true;
           
    return false;            
  }

  static const int inductive_layer_idx; 
  
  vec<int> marks_tmp;
  
  // OUTPUT from callSolver()
  vec<Lit> conflict_out;
  int      target_layer_out;  
  
  // temporaries of callSolver
  vec<int> minimark_in;
  vec<int> minimark_out;
  vec<int> rnd_perm;  
   
  int called; 
   
  bool callSolver(int idx, vec<Lit> &ma, CLOCK_CLOCKS cc,  // calls the idx-th solver, under then give assumptions ma plus the layer assumptions
                  bool compute_conflict,                   // request for returning (minimized, if flag set) appropriate conflict clause (to be delivered in conflict_out), 
                                                           // also, target_layer_out will containt index of the least delta layer on which the conflict depends (or inductive_layer_idx for "infty")
                  bool induction) {                        // allow using induction during minimization
                                                           

    MarkingSolver& solver = *solvers[idx];

    //printf("Calling for solver %d with ma ",idx); printLits(ma);
                 
    clock_StopAddPassedTime(clock_MAIN);
    clock_StartCounter(cc);

    minimark_in.clear();
    for (int i = idx; i <= phase; i++)
      minimark_in.push(i);
    minimark_in.push(inductive_layer_idx); 
    
    solver.preprocessAssumptions(ma,minimark_in);    
    bool result = (solver.simplify(),solver.solve());
    
    if (!result && compute_conflict) {
      solver.preprocessConflict(conflict_out,minimark_out);
    
      if (opt_minimize) {
        minim_attempts++;
      
        minim_solver += ma.size() - conflict_out.size();
                                 
        //turn the conflict clause back to assumptions
        for (int i = 0; i < conflict_out.size(); i++)
          conflict_out[i] = ~conflict_out[i];                                      
        solver.preprocessAssumptions(conflict_out,minimark_in);
        Lit indy = solver.getAssump(conflict_out.size() + minimark_in.size() - 1); // the translation of the induction marker, which we never plan to remove
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
          
          if (induction && opt_induction) { // inductively assume the current conflict clause            
            //abusing conflict_out for that
            conflict_out.clear();
            for (int i = 0; i < size; i++) {
              Lit l = solver.getAssump(i);
              if (l != indy && var(l) < sigsize)
                conflict_out.push(mkLit(var(l)+sigsize,!sign(l)));   // negate back and shift
            }
            conflict_out.push(goal_lit);                       
            
            marks_tmp.clear();
            marks_tmp.push(inductive_layer_idx); 
            solver.addClause(conflict_out,marks_tmp);
          }
          
          // one pass:
          for (int i = 0; i < size; i++) {
            int idx = rnd_perm[i];
            Lit save = solver.getAssump(idx);
            if (save == indy) // already removed in previous passes
              continue;

            solver.setAssump(idx,indy);
          
            if (solver.simplify(),solver.solve())
              solver.setAssump(idx,save);                          
            else {              
              minim_explicit++;
              removed_something = true;
              if (cycle_count) 
                minim_iductively++;
            }
          }
          cycle_count++;
        } while (induction && opt_induction && removed_something);       
        
        // "pushing"         
        target_layer_out = idx;        
        for (int i = 0; i < minimark_in.size()-1; i++) {
          solver.setAssump(size + i, indy);
          if (solver.simplify(),solver.solve())
            break;
          target_layer_out = minimark_in[i+1]; //makes sense even with inductive_layer_idx, which is the last value       
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
          solver.invalidateMarker(inductive_layer_idx);
          
      } else {
        target_layer_out = inductive_layer_idx;                           
        for (int i = 0; i < minimark_out.size(); i++)
          if (minimark_out[i] < target_layer_out)
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
                          
      assert(subsumes(conflict,ma));                
      
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
  
  void insertIntoSolvers(int from, int first_questionable, vec<Lit>& clause, vec<int>& markers) {  
    int stopped = 0;
    
    for (int i = from; i >= 0; i--) {
      if (!stopped && // we don't know yet      
          i <= first_questionable && //this is the first where it could happen
          i > 0 && // this layer is empty anyway
          layers[i]->isSubsumed(clause))
        stopped = i; // we could also stop inserting from this point, but maybe the weak clauses in "strong" solvers will allow for better inductive minimization (thanks to their weak marker)
    
      // TODO: test the above!!!
    
      solvers[i]->addClause(clause,markers);
    }
    
//    printf("upto %d, stopped %d\n",upto,stopped);
    
    assert(stopped < from);
    
    if (stopped+1 < least_affected_layer)
      least_affected_layer = stopped+1;    
  }
  
  bool processObligations() {
  
    while (!obligations.empty()) {
      Obligation *ob = obligations.top(); obligations.pop();
            
      int model_idx = ob->idx;            
      vec<Lit> &our_ma = ob->ma;          

      oblig_processed++;

      //printf("Obligation with model_idx %d.\n",model_idx);
      
      // TODO: does this pay off in IC3?
      if (opt_masubs && maSubsumedInLayer(our_ma,model_idx+1)) {               
        oblig_subsumed++;
               
        //printf("Subsumed\n");
        
        ob->idx++;
        if (ob->idx >= phase || !opt_resched)
          releaseObligation(ob);
        else
          obligations.push(ob);

        continue;
      }
      
      if (model_idx < model_min_layer)
        model_min_layer = model_idx;
    
      if (ob->depth > model_max_depth)
        model_max_depth = ob->depth;
                                  
      if (callSolver(model_idx,our_ma,clock_SOLVER_EXTEND,
                    true,                                  // return conflict
                    !(our_ma == initial_ma))               // induction is not correct for the initial call
                    ) {
        oblig_sat++;
      
        if (model_idx == 0) {
          printf("// SAT: model of length %d found\n",ob->depth+1);
          
          releaseObligation(ob);
          return true;
        }

        //printf("Extended\n");
        
        // going forward
        Obligation *new_ob = acquireObligation();
        if (opt_resched == 3)
          new_ob->idx = 0; //fast forward
        else if (opt_resched == 2)
          new_ob->idx = (model_idx == 1) ? 0 : model_idx-2; // a little forward
        else
          new_ob->idx = model_idx-1;                              
        
        new_ob->depth = ob->depth+1;

        MarkingSolver &model_solver = *solvers[model_idx];
        
        vec<Lit>& ma = new_ob->ma;
        ma.clear();
                                      
        for (int j = 0; j < sigsize; j++) {
          assert(model_solver.model[j+sigsize] != l_Undef);    
          if (bridge_variables[j])          
            ma.push(mkLit(j,model_solver.model[j+sigsize] == l_False));
        }                                            
        // only after the previous, so that it is sorted
        ma.push(mkLit(2*sigsize, false)); // L_initial assumed true => turning on step clauses, turning off initial clauses
                
        obligations.push(ob);        
        obligations.push(new_ob);
      } else {  //unsat                             
        oblig_unsat++;
        
        if (ob->depth == 0) { //"base level conflict"
          assert(conflict_out.size() <= 1); //only possibly the initial marker

          releaseObligation(ob); 
          
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

          // TODO: should return false here ?

        } else { // regular conflict        
          clauses_dersolver++;
          
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
          sort(conflict_out);  // ClauseSet assumes the input is sorted
                 
          bool learned_univ;
          if (target_layer_out == inductive_layer_idx) {
            learned_univ = true;
            clauses_univ++;
                                   
            //into layer
            bool res = layers.last()->insertModuloSubsumption(conflict_out);
            assert(res);
            clauses_strengthened += layers.last()->subsumed_cnt;
                                   
            //into solvers
            marks_tmp.clear();
            insertIntoSolvers(phase,model_idx,conflict_out,marks_tmp);                                  
          } else {
            learned_univ = false;
            
            if (target_layer_out == phase) //there is a possibility of learning a clause that would minimally belong to a layer that doens't exist yet
              target_layer_out = phase-1;  // we put it into the previous and a later push will move it further
          
            //into layer              
            //printf("From layer %d into layer %d: ",model_idx,target_layer_out+1); printLits(conflict_out);            
            
            bool res = layers[target_layer_out+1]->insertModuloSubsumption(conflict_out);
            assert(res);
            clauses_strengthened += layers[target_layer_out+1]->subsumed_cnt;
            
            //into solvers
            marks_tmp.clear();
            marks_tmp.push(target_layer_out+1);            
            insertIntoSolvers(target_layer_out+1,target_layer_out,conflict_out,marks_tmp);          
          }
                                                                     
          // THIS IS THE RESCHEDULING PART (we could even keep them longer, but they should die eventually, shouldn't they?):
          ob->idx++;
          if (opt_resched && 
             ob->idx < phase &&
             !learned_univ // obligation that gives rise to an universal clause is doomed to fail ever on (CAREFUL: unless it learns some other rule instead)
             ) {
            obligations.push(ob);            
          } else {
            releaseObligation(ob);    
          }
        }
      }
    }   
    return false;    
  }

  vec<Lit> initial_ma;
  
  void iterativeSearch() {
    assert(initial_ma.size() == 0);
    initial_ma.push(mkLit(2*sigsize,  true)); // not (L_initial)            
    
    layers.push(new JustClauseSet());  // the inducive layer
    
    clock_StartCounter(clock_MAIN);

    least_affected_layer = 1;
    
    for (phase = 0; ; phase++) {           
      JustClauseSet* inducive_layer = layers.last();
      layers[phase] = new JustClauseSet();         
      layers.push(inducive_layer);
      
      solvers.push(new MarkingSolver());      
      MarkingSolver &solver = *solvers.last();
            
      solver.initilazeSignature(2*sigsize+1);      
        
      vec<int> marker; /*empty*/
      
      for (int i = 0; i < rest_clauses.size(); i++)
        solver.addClause(rest_clauses[i],marker);
      
      // insert from univs
      for (JustClauseSet::Iterator it = inducive_layer->getIterator(); it.isValid(); it.next())       
        solver.addClause(it.getClause(),marker);           

      if (phase == 0) {
        marker.push(0); // but 0-th layer will remain empty
        
        // in fact, this is just the single literal single clause
        for (int i = 0; i < goal_clauses.size(); i++)
          solver.addClause(goal_clauses[i],marker);
      } else {
        // here we do the pushing               
        vec<Lit> assumps;
                
        for (int i = least_affected_layer; i < phase; i++) {
          JustClauseSet& push_layer = *layers[i];          

          for (JustClauseSet::Iterator it = push_layer.getIterator(); it.isValid(); ) {                     
            vec<Lit>const & clause = it.getClause();
            
            assumps.clear();
            for (int l = 0; l < clause.size(); l++) {
              assert(var(clause[l]) >= sigsize);
              assumps.push(mkLit(var(clause[l])-sigsize,!sign(clause[l])));
            }
            assumps.push(mkLit(2*sigsize, false));
                                   
            if (callSolver(i,assumps,clock_SOLVER_PUSH,false,false)) {  //move on
              it.next();
            } else {  // push forward 
              //could it sometimes happen that we can push a stronger version? (e.g. the conflict guy would be a proper subset?) Test it!
            
              marks_tmp.clear();
              marks_tmp.push(i+1);
            
              clauses_pushed++;      
            
              solvers[i+1]->addClause(clause,marks_tmp); //TODO: could also put into previous layers with this "weaker" marker                                        
              layers[i+1]->insertModuloSubsumption(clause);
              
              clauses_pushsubsumed += layers[i+1]->subsumed_cnt;
              
              it.remove();
            }
          }

          if (push_layer.size() == 0) {
            printf("// UNSAT: repetition detected!\n");
            if (opt_verbose)
              printf("// Delta-layer %d emptied!\n",i);            
            return;
          }
        } 
        
        least_affected_layer = phase;
      }

      if (opt_verbose && opt_pphase)
        printStatPushing(true);
      
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
        Obligation *ob = acquireObligation();      
        ob->idx = phase;
        ob->depth = 0; 
        initial_ma.copyTo(ob->ma);

        assert(obligations.size() == 0);
               
        obligations.push(ob);
                             
        if (processObligations())
          return; // problem solved                 
      }
      
      if (opt_verbose && opt_pphase)
        printStatExtending(true);        
      
      if (opt_phaselim && phase >= opt_phaselim) {
        printf("// UNRESOLVED: phase limit reached!\n");
        return;
      }
    }
  }
};

const int SolvingContext::inductive_layer_idx = INT_MAX;  

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

static void analyzeSpec(int sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  SolvingContext& context = *global_context;
  
  Lit goal_lit = lit_Undef;
     
  clock_StartCounter(clock_SIMP);      
      
  { // preprocessing    
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
    
    int new_var_count = 0;
    vec<Var> renaming;
    
    vec<bool>& bridge_variables = context.bridge_variables;    
    
    for (int i = sigsize; i < 2*sigsize+2; i++) { // the two markers didn't get eliminated!
      renaming.push();
      
      if (!simpSolver.isEliminated(i)) { // the goal_lit goes in as well, that's why ma_subsumption testing works!
        bridge_variables.push(simpSolver.isFrozen(i));
        renaming.last() = new_var_count++;
      } else
        renaming.last() = var_Undef;  
    }
    
    new_sigsize = new_var_count - 2; //the two markers don't count
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
      
      //printf("%s clause: ",goal ? "Goal" : "Normal"); printClause(clause);
      
      Clauses& target = (goal ? context.goal_clauses : context.rest_clauses);

      int idx = target.size();
      target.push();
      clause.moveTo(target[idx]);            
    }
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
}

//=================================================================================================

void ensure_single_unit_goal(int &sigsize, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  if (goal.size() == 1 && goal[0].size() == 1)
    return;
    
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
}

static void SIGINT_exit(int signum) {
  printf("// *** INTERRUPTED ***\n");
  if (opt_verbose)
    global_context->printGOStat();
  fflush(stdout);
  _exit(1); 
}

void testJustClauseSet() {
  JustClauseSet cs;  
  vec<Lit> cl;

  int call = 0;
  
  for (int k = 0; k < 5; k++) {
    cl.clear();
    for (int l = 0; l < 4; l++)
      cl.push(toLit(rand() & 7));
  
    sort(cl);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < cl.size(); i++)
      if (cl[i] == ~p)
        goto next_clause;
      else if (cl[i] != p)
        cl[j++] = p = cl[i];
    cl.shrink(i - j);          
    
    printf("Call (%d) - inserting: ",++call); printLits(cl);   
                
    cs.insertModuloSubsumption(cl);       
    cs.visualize();        
    next_clause: ;
  }
  
  JustClauseSet::Iterator it1 = cs.getIterator();
  //it1.next();
  it1.remove();
  cs.visualize();
  
  JustClauseSet::Iterator it2 = cs.getIterator();
     
  it2.remove();
  
  cs.visualize();
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

    //testJustClauseSet();
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
    
    aiger_LoadSpec((argc == 1) ? 0 : argv[1], (int)opt_reversed, (int)opt_pg, /*no parsing chat*/0, opt_kth_property, (int)false,
                   sigsize,initial,goal,universal,step);

    clock_StopPassedTime(clock_PARSE);
    
    if (opt_verbose)
      printf("// Loaded spec -- sigsize: %d, #initial: %d, #goal: %d, #universal: %d, #step: %d\n",sigsize,initial.size(),goal.size(),universal.size(),step.size());

    ensure_single_unit_goal(sigsize,initial,goal,universal,step);        
    
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

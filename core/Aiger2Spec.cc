
#include "core/Aiger2Spec.h"

using namespace Minisat;

#include <string.h>
#include <stdlib.h>
#include <limits.h>
#include <stdarg.h>

extern "C" {
#include "aiger.h"
}

static void
msg (const char *fmt, ...)
{
  va_list ap;
  fputs ("[aig2spec] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
wrn (const char *fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fputs ("[aig2spec] WARNING ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
die (const char *fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fputs ("*** [aig2spec] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  exit (1);
}

void aiger_LoadSpec(const char* input_name, int reversed, int pg, int verbose, int kth_property, int parse_liveness,
                    int &signature_size, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step) {
  const char  *error;
  int recheck, cycles;
  unsigned i, * refs, lit, rhs0, rhs1, next, reset;
  aiger_t *aiger;
  
  aiger_symbol *the_output = 0;
  aiger_symbol *the_justice = 0;

  aiger = aiger_init ();

  if (input_name)
    error = aiger_open_and_read_from_file (aiger, input_name);
  else
    error = aiger_read_from_file (aiger, stdin);

  if (error)
    die ("%s: %s", input_name ? input_name : "<stdin>", error);

  if (kth_property == -2) { // just print the ids and abort    
    for (i = 0; i < (parse_liveness ? aiger->num_justice : aiger->num_outputs + aiger->num_bad); i++)
      printf("%s -id=%d\n",input_name ? input_name : "", i);
    exit (0);
  }
    
  if (verbose)
     msg ("read MILOABCJF %u %u %u %u %u %u %u %u %u", 
       aiger->maxvar,
       aiger->num_inputs,
       aiger->num_latches,
       aiger->num_outputs,
       aiger->num_ands,
       aiger->num_bad,
       aiger->num_constraints,
       aiger->num_justice,
       aiger->num_fairness);
         
  // analyze the input and select the_output gate
  if (parse_liveness) { // for liveness
    if (reversed)
      die ("cannot reverse liveness properties");
  
    if (aiger->num_outputs > 0)
      wrn ("ignoring outputs");
      
    if (aiger->num_bad > 0)
      wrn ("ignoring bad state properties");
  
    if (!aiger->num_justice)
      die ("no justice property specified");
  
    if (kth_property < 0) { // pick the only one         
      if (aiger->num_justice > 1)
        die ("more than one justice property specified");
    
      the_justice = aiger->justice;
    
    } else { // pick the selected one
      if ((unsigned)kth_property >= aiger->num_justice)
        die("property index out of range");
    
      the_justice = aiger->justice + kth_property;
    }    
  } else { // for reachability  
    if (aiger->num_outputs > 0 && aiger->num_bad > 0) {
      wrn ("the problem combines both simple outputs and explicit bad state properties%s",kth_property >= 0 ? ".\n Reindexed in this order" : "");
    }
  
    if (aiger->num_outputs + aiger->num_bad == 0)
      die ("no output or bad state property specified");
         
    if (kth_property < 0) { // pick the only one
      if (aiger->num_outputs + aiger->num_bad > 1)
        die ("more than one output or bad state property specified");  
    
      if (aiger->num_outputs)    
        the_output = aiger->outputs;
      else
        the_output = aiger->bad;
    
    } else { // pick the selected one
      if ((unsigned)kth_property >= aiger->num_outputs + aiger->num_bad)
        die ("property index out of range");
    
      if ((unsigned)kth_property < aiger->num_outputs)
        the_output = aiger->outputs + kth_property;
      else
        the_output = aiger->bad + (kth_property - aiger->num_outputs);
    }    
     
    if (aiger->num_justice) 
      wrn ("ignoring justice properties");
    if (aiger->num_fairness) 
      wrn ("ignoring fairness constraints (finite trace semantics!)");  
  }
  
  // currently prepared clause
  vec<Lit> cur_clause;
  
  aiger_reencode (aiger);

  signature_size = aiger->maxvar+1; //one additional var for the "constant zero"  
  
  if (!parse_liveness && the_output->lit == 0) {
    if (verbose) msg ("trivially unsat");      
    universal.push(cur_clause); // the empty clause
    cur_clause.clear();
  } else if (!parse_liveness && the_output->lit == 1) {
    if (verbose) msg ("trivially sat"); 
    // empty input 
  } else {
  
      refs = (unsigned*)calloc (2*(aiger->maxvar+1), sizeof *refs);
      
      if (parse_liveness) { 
        // all the literals of the selected justice property
        for (i = 0; i < the_justice->size; i++) {
          lit = the_justice->lits[i];
          refs[lit]++;
        }
        
        // all the fairness constraints
        for (i = 0; i < aiger->num_fairness; i++) {
          lit = aiger->fairness[i].lit;
          refs[lit]++;
        }        
      } else {              
        // the one selected output      
        lit = the_output->lit;
        refs[lit]++;
      }
      
      // all the contraints - in any case
      for (i = 0; i < aiger->num_constraints; i++) {
        lit = aiger->constraints[i].lit;
        refs[lit]++;
      }
                 
      recheck = 1;
      cycles = 0;
            
      while (recheck) 
  {
    recheck = 0;
    cycles++;
  
    // propagate through and-gates
    i = aiger->num_ands; 
    while (i--)
    {
      lit  = aiger->ands[i].lhs;
      if (refs[lit]) 
        {
          refs[aiger->ands[i].rhs0]++;
          refs[aiger->ands[i].rhs1]++;
        }
      if (refs[aiger_not (lit)]) 
        {
          refs[aiger_not (aiger->ands[i].rhs0)]++;
          refs[aiger_not (aiger->ands[i].rhs1)]++;
        }
    }
    
    // new requests from affected latches?
    for (i = 0; i < aiger->num_latches; i++)
    {
      lit = aiger->latches[i].lit;  
      next = aiger->latches[i].next;
      if (refs[lit] && !refs[next]) {
        refs[next]++;
        recheck++;
      }
      
      if (refs[aiger_not (lit)] && !refs[aiger_not (next)]) {
        refs[aiger_not (next)]++;
        recheck++;
      } 
    }
  }

  if (verbose) msg ("Transitive COI computed in %d iterations.\n",cycles);
  
      if (!pg)
	{
	  for (lit = 2; lit <= 2*aiger->maxvar+1; lit++)
	    refs[lit] = INT_MAX;
	}
      
      // the always_zero_variable
      if (refs[0] || refs[1]) {
        cur_clause.push(mkLit(0,true)); // negated zero
        universal.push(cur_clause);
        cur_clause.clear();
      }
                            
      // the and-gates
      for (i = 0; i < aiger->num_ands; i++)
	{
    lit  = aiger->ands[i].lhs;
    rhs0 = aiger->ands[i].rhs0;
    rhs1 = aiger->ands[i].rhs1;
	  if (refs[lit])
	    {               
        cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));  
        cur_clause.push(mkLit(aiger_lit2var(rhs1),aiger_sign(rhs1)));  
        universal.push(cur_clause);
        cur_clause.clear();
      
        cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));
        cur_clause.push(mkLit(aiger_lit2var(rhs0),aiger_sign(rhs0)));
        universal.push(cur_clause);
        cur_clause.clear();                         
	    }
	  if (refs[lit+1])
	    {
        cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        cur_clause.push(mkLit(aiger_lit2var(rhs1),!aiger_sign(rhs1)));
        cur_clause.push(mkLit(aiger_lit2var(rhs0),!aiger_sign(rhs0)));
        universal.push(cur_clause);
        cur_clause.clear();             
	    }
	}
  
      // the latches
      for (i = 0; i < aiger->num_latches; i++)
  {
    lit   = aiger->latches[i].lit;
    reset = aiger->latches[i].reset;
    next  = aiger->latches[i].next;
    
    // init (reset)
    if ((reset == 0) && refs[lit])
      {
        cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));
        (reversed ? goal : initial).push(cur_clause);
        cur_clause.clear();
      }
    else if ((reset == 1) && refs[aiger_not (lit)])
      {       
        cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        (reversed ? goal : initial).push(cur_clause);
        cur_clause.clear();
      }
    else ; // undefined = no constraint
    
    // next value
	  if (refs[lit])
	    {
        if (reversed) {
          cur_clause.push(mkLit(aiger_lit2var(next)+signature_size,aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit),!aiger_sign(lit)));
        } else {
          cur_clause.push(mkLit(aiger_lit2var(next),aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit)+signature_size,!aiger_sign(lit)));
        }
        step.push(cur_clause);
        cur_clause.clear();             
      }
      
    if (refs[lit+1])
	    {
        if (reversed) {
          cur_clause.push(mkLit(aiger_lit2var(next)+signature_size,!aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        } else {
          cur_clause.push(mkLit(aiger_lit2var(next),!aiger_sign(next)));
          cur_clause.push(mkLit(aiger_lit2var(lit)+signature_size,aiger_sign(lit)));
        }
        step.push(cur_clause);
        cur_clause.clear();               
      }       
  }
      
      if (parse_liveness) {
      
        // TODO !!!
      
      } else {
        //the unit goal clause
        cur_clause.push(mkLit(aiger_lit2var(the_output->lit),aiger_sign(the_output->lit)));
        (reversed ? initial : goal).push(cur_clause);
        cur_clause.clear();      
      }
      
      // the contraints -- unit clauses
      for (i = 0; i < aiger->num_constraints; i++) {
        lit = aiger->constraints[i].lit;
        cur_clause.push(mkLit(aiger_lit2var(lit),aiger_sign(lit)));
        universal.push(cur_clause);
        cur_clause.clear();                    
      }
      
      free (refs);
    }

  aiger_reset (aiger);
}
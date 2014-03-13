/****************************************************************************************[Dimacs.h]
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

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "utils/ParseUtils.h"
#include "core/SolverTypes.h"

typedef Minisat::vec< Minisat::vec< Minisat::Lit> > Clauses;

namespace Minisat {

static void readClause(StreamBuffer& in, int sigsize, bool large, bool reversed, vec<Lit>& lits) {
    int parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        
        if (var >= (large ? 2*sigsize : sigsize))
          printf("PARSE ERROR! Large variable index.\n"), exit(3);
        
        if (large && reversed)
          var = (var < sigsize) ? var + sigsize : var - sigsize;
        
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

static void parse_DIMACS_main(StreamBuffer& in, bool reversed, int &signature_size, Clauses &initial, Clauses &universal, Clauses &goal, Clauses &step) {
  vec<Lit> lits;
    
  signature_size = 0;
  Clauses* target = 0;
  int cl_to_go = 0;
    
  for (;;) {
    skipWhitespace(in);
    if (*in == EOF) break;
              
    if (*in == 'i') {
      if (eagerMatch(in, "i cnf")) {
        if (cl_to_go != 0)
          printf("PARSE ERROR! Wrong number of clauses promised.\n(reading i and cl_to_go=%d)\n",cl_to_go), exit(3);
      
        if (!target) { // first read
          signature_size = parseInt(in);          
        } else { // confirmation
          if (signature_size != parseInt(in))
            printf("PARSE ERROR! Inconsitent signature size.\n"), exit(3);          
        }
        cl_to_go = parseInt(in);

        target = reversed ? &goal : &initial;
      } else {
        printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
      }
    } else if (*in == 'u') {
      if (eagerMatch(in, "u cnf")) {
        if (cl_to_go != 0)
          printf("PARSE ERROR! Wrong number of clauses promised.\n(reading u and cl_to_go=%d)\n",cl_to_go), exit(3);
      
        if (!target) { // first read
          signature_size = parseInt(in);          
        } else { // confirmation
          if (signature_size != parseInt(in))
            printf("PARSE ERROR! Inconsitent signature size.\n"), exit(3);          
        }
        cl_to_go = parseInt(in);

        target = &universal;
      } else {
        printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
      }
    } else if (*in == 'g') {
      if (eagerMatch(in, "g cnf")) {
        if (cl_to_go != 0)
          printf("PARSE ERROR! Wrong number of clauses promised.\n(reading g and cl_to_go=%d)\n",cl_to_go), exit(3);
      
        if (!target) { // first read
          signature_size = parseInt(in);          
        } else { // confirmation
          if (signature_size != parseInt(in))
            printf("PARSE ERROR! Inconsitent signature size.\n"), exit(3);          
        }
        cl_to_go = parseInt(in);

        target = reversed ? &initial : &goal;
      } else {
        printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
      }
    } else if (*in == 't') {
      if (eagerMatch(in, "t cnf")) {
        if (cl_to_go != 0)
          printf("PARSE ERROR! Wrong number of clauses promised.\n(reading t and cl_to_go=%d)\n",cl_to_go), exit(3);
      
        if (!target) { // first read                 
          signature_size = parseInt(in);
          if (signature_size & 1)
            printf("PARSE ERROR! Transition signature of odd size.\n"), exit(3);
            
          signature_size >>= 1;
        } else { // confirmation
          if (2*signature_size != parseInt(in))
            printf("PARSE ERROR! Inconsitent signature size.\n"), exit(3);          
        }
        cl_to_go = parseInt(in);

        target = &step;
      } else {
        printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
      }
    } else if (*in == 'c') {
      skipLine(in);
    } else {    
      readClause(in, signature_size, target == &step, reversed, lits);
      target->push(lits);
      cl_to_go--;           
    }
  }

  if (cl_to_go != 0)
    printf("PARSE ERROR! Wrong number of clauses promised.\n(reading EOF and cl_to_go=%d)\n",cl_to_go), exit(3);
}

static void dimacs_LoadSpec(
        /* input:*/ 
        const char* input_name, // can be 0 for parsing stdin
        bool reversed,
        /*output:*/ int &signature_size, Clauses &initial, Clauses &universal, Clauses &goal, Clauses &step) {

  gzFile input_stream = input_name ? gzopen(input_name, "rb") : gzdopen(0, "rb");   
  if (input_stream) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, reversed, signature_size, initial, universal, goal, step);
    gzclose(input_stream);
  } else {
    printf("Couldn't open file %s!\n",input_name);
    exit(1);
  }
}        
    
//=================================================================================================
}

#endif

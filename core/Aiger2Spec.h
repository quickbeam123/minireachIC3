
#ifndef Aiger_2_Spec_h
#define Aiger_2_Spec_h

#include "mtl/Vec.h"
#include "core/SolverTypes.h"

typedef Minisat::vec< Minisat::vec<Minisat::Lit> > Clauses;

void aiger_LoadSpec( /* input:*/ 
                        const char* input_name, // can be 0 for parsing stdin
                        int reversed,
                        int pg,
                        int verbose,
                        int kth_property,       // can be -1 to expect exactly one property and return it
                        int parse_liveness,     // looks for liveness property instead of bad state
                     /*output:*/ int &signature_size, Clauses &initial, Clauses &goal, Clauses &universal, Clauses &step);

#endif
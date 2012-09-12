#ifndef ClauseSet_h
#define ClauseSet_h

#include "core/SolverTypes.h"
#include "mtl/Vec.h"

#include <stdio.h>

namespace Minisat {

inline bool clause_sorted(vec<Lit> const & cl) {
  for (int i = 1; i < cl.size(); i++)
    if (!(cl[i-1] < cl[i]))
      return false;
  return true;
}

inline bool subsumes(const vec<Lit> &c1, const vec<Lit> &c2) { // assumed sorted
  vec<int> dummy;
  
  //printf("\n");
  //printClause(c1,dummy);
  //printClause(c2,dummy);

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

inline void printLits(const vec<Lit> &lits) {
  for (int i = 0; i < lits.size(); i++)  
    printf("%s%d ",sign(lits[i])?"-":"",var(lits[i]));    
  printf("\n");
}

struct JustClause {};

// TODO: it is not just compare -- new name ???

struct JustClauseCompare {
  static const JustClause dummy;

  bool smallerEqualThan(JustClause const & first, JustClause const & second) const { return true; }
  void dispose(JustClause elem) { return; }
};

template<class T, class C >
class ClauseSet {
  /* can be empty, but cannot contain the empty clause */

  C compare;
   
  struct Node {
    Lit val;
    Node *down,*right;
    vec<T> elems;
    
    Node(Lit _val, T const & elem) : val(_val), down(0), right(0) { elems.push(elem); }
    Node(Lit _val, Node* _down, Node* _right) : val(_val), down(_down), right(_right) {}    
  };
    
  int sz;
  Node* top;
   
  void releaseNodes(Node* node);
  void releaseSubsumedNodes(Node*& node, T const& elem, bool go_right = true);
  void removeSubsumedElems(Node& node, T const& elem);
  bool subsumedClauseByNodes(Node* node, vec<Lit> const & clause, int pos, T const& elem) const;     
  bool subsumed(Node* node, vec<Lit> const & clause, int pos, T const& elem) const; 
  void prune(Node*& node, vec<Lit> const & clause, int pos, T const& elem);     
  Node* createChain(vec<Lit> const & clause, int pos, T const& elem);  
  bool insertion(Node*& node, vec<Lit> const & clause, int pos, T const& elem);  
  bool equals(Node* one, Node* other) const;     
       
  void visualizeRec(Node* node, vec<bool>& stack) {
    if (node) {
      for (int i = 0; i < stack.size(); i++)
        printf("%s",stack[i] ? "D" : "R");
      printf(" %s%d[%d]\n",sign(node->val) ? "-" : "", var(node->val),node->elems.size());
      stack.push(true);
      visualizeRec(node->down,stack);
      stack.last() = false;
      visualizeRec(node->right,stack);
      stack.pop();    
    }  
  }   
   
public:
  int nodes_created;
  int nodes_freed;

  ClauseSet() : compare(C()), sz(0), top(0), nodes_created(0), nodes_freed(0) {}
  ClauseSet(C c) : compare(c), sz(0), top(0), nodes_created(0), nodes_freed(0) {}
  ~ClauseSet() {
    releaseNodes(top);
    // printf("Released nodes - size is %d\n",sz); fflush(stdout);
    assert(nodes_created == nodes_freed);
    assert(sz==0); 
    }

  int size() const { return sz; }
  
  bool operator==(const ClauseSet<T,C>& other) const {
    if (other.sz != sz)
      return false;

    return equals(top,other.top);
  }
   
  struct Iterator { // Implements in-order traversal
    friend class ClauseSet;
  
    bool isValid() {
      return stack.size() > 0;
    }
    
    vec<Lit> const & getClause() {
      return clause;    
    }
    
    T const & getElem() {
      return (*stack.last())->elems[pos];
    }
    
    void next() {
      while (stack.size() > 0) {
        if (++pos < (*stack.last())->elems.size()) 
          return;
          
        clause.pop();
          
        if ((*stack.last())->right)  // current element stays on the stack (because of deletion)                   
          return rolldown(&(*stack.last())->right);        
        
        Node** last_top;
        do {
          last_top = stack.last();
          stack.pop();
        } while (stack.size() > 0 && last_top == &(*stack.last())->right);
             
        pos = -1;
      }
    }
    
    // after removal we point to the next element (if any)
    void remove() {
      owner.sz--;
    
      assert(stack.size() > 0);
      assert(pos < (*stack.last())->elems.size());
                 
      //just kill a non-last element
      if (pos < (*stack.last())->elems.size()-1) {
        (*stack.last())->elems[pos] = (*stack.last())->elems.last();
        (*stack.last())->elems.pop();
        return;
      }
            
      (*stack.last())->elems.pop(); //kills the last one
            
      if ((*stack.last())->down) 
        return next();           
            
      do {
        assert(!(*stack.last())->down);
      
        //node dying:
        Node* dier = *stack.last();
        Node** repair = stack.last();
        
        stack.pop();
        clause.pop();
        
        // dier->right could be 0        
        *repair = dier->right; 
                
        if (dier->right) { // it was != 0        
          owner.nodes_freed++;
          delete dier;

          return rolldown(repair);
        }

        // it was == 0                             
        
        if (stack.size() == 0) {
          owner.nodes_freed++;
          delete dier;
          return;
        }                    

        if (repair == &(*stack.last())->right) {     // been "right" of somebody  
          // continue as if in next()
          do {
            repair = stack.last();
            stack.pop();
          } while (stack.size() > 0 && repair == &(*stack.last())->right);
          pos = -1;
          
          owner.nodes_freed++;
          delete dier;
          return next();
        }
            
        owner.nodes_freed++;
        delete dier;
      } while ((*stack.last())->elems.size() == 0);
            
      pos = 0;            
    }
    
    private:
      ClauseSet& owner;
      
      int pos;
      vec<Node**> stack;
      vec<Lit> clause;
      
      void rolldown(Node** node) {
        assert(*node);
        pos = 0;
        do {
          stack.push(node);
          clause.push((*node)->val);
          node = &(*node)->down;
        } while (*node);
        assert((*stack.last())->elems.size() > 0);
      }
      
      Iterator(ClauseSet& o) : owner(o) {
        if (o.top)
          rolldown(&o.top);
      }
  };
   
  Iterator getIterator() {
    return Iterator(*this);
  }

  int subsumed_cnt;
  
  /* assumes and will keep the set subsumption reduced */
  bool insertModuloSubsumption(vec<Lit>const & clause, T const & elem = C::dummy) {
    assert(clause.size() > 0 && clause_sorted(clause));    
    
    /*

    int oldsz = sz;
    
    bool killed = 0;
    int kills = 0;
           
    for (Iterator it = getIterator(); it.isValid(); it.next()) {         
      if (subsumes(it.getClause(),clause) && compare.smallerEqualThan(it.getElem(),elem))
        killed = true;
      else if (subsumes(clause,it.getClause()) && compare.smallerEqualThan(elem,it.getElem()))
        kills++;     
    }
    */
    
    subsumed_cnt = sz;

    bool res = insertion(top,clause,0,elem);
    
    subsumed_cnt = subsumed_cnt - sz + 1;
    assert(subsumed_cnt >= 0);
    
    /*
    printf("Oldsz %d, sz %d, Res: %d, killed %d, kills %d\n", oldsz, sz, res, killed, kills);
                       
    assert(res != killed);
    assert(!killed || kills==0); //if not inserted it couldn't have subsumed
    assert((int)sz == oldsz-kills + (killed ? 0 : 1));    
    
    int calls = 0;
    for (Iterator it = getIterator(); it.isValid(); it.next())
      calls++;
    
    // printf("sz %d, calls %d\n",sz,calls);
    
    assert(sz == calls);
    */
    
    return res;
  }

  bool isSubsumed(vec<Lit> const & clause, T const & elem = C::dummy) const {
    assert(clause_sorted(clause));  
    if (!top) return false;    
    return subsumed(top,clause,0,elem);
  }
     
  void visualize() {
    vec<bool> stack;
    printf("Visualizing %d stored clauses:\n",sz);    
    visualizeRec(top, stack);
  }    
};

typedef ClauseSet<JustClause,JustClauseCompare> JustClauseSet;

template<class T, class C>
bool ClauseSet<T,C>::subsumedClauseByNodes(Node* node, vec<Lit> const & clause, int pos, T const& elem) const {
  assert(node);
  assert(pos < clause.size());
  assert(!(node->val < clause[pos]));
  
  while (clause[pos] < node->val) //going forward in the clause
    if (!(++pos < clause.size())) 
      return false;

  if (node->val < clause[pos])
    return false;
  
  // equal
  for (int i = 0; i < node->elems.size(); i++)
    if (compare.smallerEqualThan(node->elems[i],elem))
      return true;
             
  return node->down && subsumed(node->down,clause,pos+1,elem);
}

template<class T, class C>
bool ClauseSet<T,C>::subsumed(Node* node, vec<Lit> const & clause, int pos, T const& elem) const {
  assert(node);
  
  if (!(pos < clause.size()))
    return false;
  
  do { // going right along nodes 
    if (node->val < clause[pos])
      return false;

    if (subsumedClauseByNodes(node,clause,pos,elem))
      return true;
      
    node = node->right;
  } while (node);
  
  return false;    
}

template<class T, class C>
void ClauseSet<T,C>::releaseNodes(Node* node) {    
  while (node) { // going right along nodes
    sz -= node->elems.size();
    if (node->down)
      releaseNodes(node->down);    
                     
    Node* dier = node;
    node = node->right;
    delete dier;
    nodes_freed++;
  }
}

template<class T, class C>
void ClauseSet<T,C>::removeSubsumedElems(Node& node, T const& elem) {  
  int i,j;
  for (i = 0, j = 0; i < node.elems.size(); i++)
    if (compare.smallerEqualThan(elem,node.elems[i])) {
      compare.dispose(node.elems[i]);
      sz--;
    } else
      node.elems[j++] = node.elems[i];
  node.elems.shrink(i-j);
}

template<class T, class C>
void ClauseSet<T,C>::releaseSubsumedNodes(Node*& node, T const& elem, bool go_right) {
  if (!node)
    return;

  removeSubsumedElems(*node,elem);
  releaseSubsumedNodes(node->down,elem);  
  if (go_right)
    releaseSubsumedNodes(node->right,elem);    
       
  if (node->elems.size()==0 && !node->down) {
    Node* dier = node;
    node = node->right;
    delete dier;
    nodes_freed++;
  }
}

template<class T, class C>
void ClauseSet<T,C>::prune(Node*& node, vec<Lit> const & clause, int pos, T const& elem) {
  assert(node);
  assert(pos < clause.size());
     
  // go right with recursion first (TODO: strictly speaking, this goes against the preorder traversal style)
  if (node->right)
    prune(node->right,clause,pos,elem);
  
  if (clause[pos] < node->val)
    return;
     
  if (node->val == clause[pos]) {
    ++pos;
    if (pos == clause.size()) {  //last literal matched    
      releaseSubsumedNodes(node,elem,false);
      return;         
    }
  }
  
  assert(node->val < clause[pos]);
  
  if (node->down) {
    prune(node->down,clause,pos,elem);
    if (node->elems.size()==0 && !node->down) {
      Node *replace = node->right;
      delete node;
      nodes_freed++;
      node = replace;
    }
  }
}

template<class T, class C>
typename ClauseSet<T,C>::Node* ClauseSet<T,C>::createChain(vec<Lit> const & clause, int pos, T const& elem) {
  assert(pos < clause.size());
  
  int tpos = clause.size();  
  Node* result = new Node(clause[--tpos],elem);
  nodes_created++;
  while (pos < tpos) {
    nodes_created++;
    result = new Node(clause[--tpos],result,0);
  }   
  return result;
}

// returns true if the clause was inserted; otherwise it was subsumed (or present)
template<class T, class C>
bool ClauseSet<T,C>::insertion(Node*& node, vec<Lit> const & clause, int pos, T const& elem) {
  assert(pos < clause.size());
  
  if (!node) {
    node = createChain(clause,pos,elem); 
    sz++;
    return true;  
  }
  
  if (node->val < clause[pos]) {
    prune(node,clause,pos,elem);
    Node* chain = createChain(clause,pos,elem);
    chain->right = node;
    node = chain; 
    sz++;
    return true;
  }
  
  if (node->val == clause[pos]) {      
    // subsumed ? 
    for (int i = 0; i < node->elems.size(); i++)
      if (compare.smallerEqualThan(node->elems[i],elem))
        return false;

    if (pos+1 < clause.size()) {
      if (insertion(node->down,clause,pos+1,elem)) {
        if (node->right)
          prune(node->right,clause,pos,elem);
        return true;
      }
      return false;
    } else {
      // derived to our destination
      removeSubsumedElems(*node,elem);
      node->elems.push(elem);
      sz++;
      
      if (node->right)
        prune(node->right,clause,pos,elem);
              
      releaseSubsumedNodes(node->down,elem);
                        
      return true;
    }
  }

  if (subsumedClauseByNodes(node,clause,pos,elem))
    return false;

  return insertion(node->right,clause,pos,elem);  
}

template<class T, class C>
bool ClauseSet<T,C>::equals(Node* one, Node* other) const {
  if (!one)
    return (other == 0);

  if (!other)
    return false;
  
  if (one->val != other->val)
    return false;
    
  // TODO: should contain the same elements also in this node
  // - compare should also implement equality test and would pair them up
  // - not implemented (yet), because not needed
  
  if (!equals(one->down,other->down))
    return false;
    
  return equals(one->right,other->right);
}

}

#endif

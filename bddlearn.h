#pragma once

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <list>
#include <boost/dynamic_bitset.hpp>
#include "aig.hpp"

typedef struct BddMan_ BddMan;
struct BddMan_ {
  int                nVars;         // the number of variables
  int                nObjs;         // the number of nodes used
  int                nObjsAlloc;    // the number of nodes allocated
  int *              pUnique;       // unique table for nodes
  int *              pNexts;        // next pointer for nodes
  int *              pCache;        // array of triples <arg0, arg1, AND(arg0, arg1)>
  int *              pObjs;         // array of pairs <cof0, cof1> for each node
  unsigned short *   pVars;         // array of variables for each node
  unsigned char *    pMark;         // array of marks for each BDD node
  unsigned short *   pLevels;
  unsigned short *   pRefs;
  unsigned           nUniqueMask;   // selection mask for unique table
  unsigned           nCacheMask;    // selection mask for computed table
  int                nCacheLookups; // the number of computed table lookups
  int                nCacheMisses;  // the number of computed table misses

  int nMinRemoved;

  unsigned * pEdges;
  std::vector<std::list<int> > nodelist;
  unsigned short reolowvar;
};

static inline int Var2Lit(int i, bool c) { return i << 1 + (int)c; }
static inline int Lit2Var(int i) { return i >> 1; }
static inline int LitIsCompl(int i) { return i & 1; }
static inline int LitRegular(int i) { return i & ~1; }
static inline int LitNot(int i) { return i ^ 1; }
static inline int LitNotCond(int i, bool c) { return i ^ (int)c; }

static inline int BddIthVar(int i) { return Var2Lit(i + 1, 0); }
static inline unsigned BddHash(int Arg0, int Arg1, int Arg2) { return 12582917 * Arg0 + 4256249 * Arg1 + 741457 * Arg2; }

static inline int BddVar2Level(BddMan * p, int i) { return p->pLevels[i]; }
static inline int BddLevel2Var(BddMan * p, int i) {
  for(int v = 0; v < p->nVars; v++)
    if(i == p->pLevels[v])
      return v;
  abort();
}

static inline int BddVar(BddMan * p, int i) { return p->pVars[Lit2Var(i)]; }
static inline int BddLevel(BddMan * p, int i) { return BddVar2Level(p, BddVar(p, i)); }
static inline int BddThen(BddMan * p, int i) { return LitNotCond(p->pObjs[LitRegular(i)], LitIsCompl(i)); }
static inline int BddElse(BddMan * p, int i) { return LitNotCond(p->pObjs[LitRegular(i)+1], LitIsCompl(i)); }

static inline int BddMark(BddMan * p, int i) { return p->pMark[Lit2Var(i)]; }
static inline void BddSetMark(BddMan * p, int i, int m){ p->pMark[Lit2Var(i)] = m; }

static inline unsigned BddEdge(BddMan * p, int i) { return p->pEdges[Lit2Var(i)]; }
static inline void BddIncEdge(BddMan *p, int i) { if(i == 0 || i == 1) return; assert(p->pEdges[Lit2Var(i)] != 0xffffffff); p->pEdges[Lit2Var(i)]++; }
static inline void BddDecEdge(BddMan *p, int i) { if(i == 0 || i == 1) return; assert(p->pEdges[Lit2Var(i)]); p->pEdges[Lit2Var(i)]--; }

static inline unsigned BddPEdge(BddMan * p, int i) { return p->pEdges[Lit2Var(i)] & 0xffff; }
static inline void BddIncPEdge(BddMan *p, int i) { if(i == 0 || i == 1) return; assert((p->pEdges[Lit2Var(i)] & 0xffff) != 0xffff); p->pEdges[Lit2Var(i)]++; }
static inline void BddDecPEdge(BddMan *p, int i) { if(i == 0 || i == 1) return; assert(p->pEdges[Lit2Var(i)] & 0xffff); p->pEdges[Lit2Var(i)]--; }
static inline unsigned BddNEdge(BddMan * p, int i) { return p->pEdges[Lit2Var(i)] >> 16; }
static inline void BddIncNEdge(BddMan *p, int i) { if(i == 0 || i == 1) return; assert((p->pEdges[Lit2Var(i)] >> 16) != 0xffff); p->pEdges[Lit2Var(i)] += 0x10000; }
static inline void BddDecNEdge(BddMan *p, int i) { if(i == 0 || i == 1) return; assert(p->pEdges[Lit2Var(i)] >> 16); p->pEdges[Lit2Var(i)] -= 0x10000; }

static inline int BddRef(BddMan * p, int i) { return p->pRefs[Lit2Var(i)]; }
static inline void BddIncRef(BddMan *p, int i) { if(p->pRefs[Lit2Var(i)] == 0xffff) return; p->pRefs[Lit2Var(i)]++; }
static inline void BddDecRef(BddMan *p, int i) { if(p->pRefs[Lit2Var(i)] == 0xffff) return; assert(p->pRefs[Lit2Var(i)]); p->pRefs[Lit2Var(i)]--; }
static inline void BddPrintRef(BddMan *p) {
  std::cout << "ref nodes :" << std::endl;
  for(int i = p->nVars + 1; i < p->nObjs; i++) {
    if(p->pRefs[i] == 0xffff)
      std::cout << "*" << i << std::endl;
    else if(p->pRefs[i])
      std::cout << i << std::endl;
  }
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************
   Synopsis    [Creating new node.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddUniqueCreateInt(BddMan * p, int Var, int Then, int Else) {
  int *q = p->pUnique + (BddHash(Var, Then, Else) & p->nUniqueMask);
  for(; *q; q = p->pNexts + *q)
    if((int)p->pVars[*q] == Var && p->pObjs[*q+*q] == Then && p->pObjs[*q+*q+1] == Else)
      return Var2Lit(*q, 0);
  if(p->nObjs == p->nObjsAlloc) {
    for(; p->nMinRemoved < p->nObjsAlloc; p->nMinRemoved++)
      if(p->pVars[p->nMinRemoved] == 0xffff)
	break;
    if(p->nMinRemoved == p->nObjsAlloc)
      return -1;
    *q = p->nMinRemoved++;
  }
  else *q = p->nObjs++;
  p->pVars[*q] = Var;
  p->pObjs[*q+*q] = Then;
  p->pObjs[*q+*q+1] = Else;
  //printf("Added node %3d: Var = %3d.  Then = %3d.  Else = %3d\n", *q, Var, Then, Else);
  assert(!LitIsCompl(Else));
  return Var2Lit(*q, 0);
}
void BddGarbageCollect(BddMan * p);
int BddUniqueCreate(BddMan * p, int Var, int Then, int Else) {
  assert(Var >= 0 && Var < p->nVars);
  assert(BddVar2Level(p, Var) < BddLevel(p, Then));
  assert(BddVar2Level(p, Var) < BddLevel(p, Else));
  if(Then == Else) return Else;
  bool c = LitIsCompl(Else);
  if(c) Then = LitNot(Then), Else = LitNot(Else);
  int r = BddUniqueCreateInt(p, Var, Then, Else);
  if(r < 0) {
    BddGarbageCollect(p);
    r = BddUniqueCreateInt(p, Var, Then, Else);
    assert(r > 0);
  }
  return LitNotCond(r, c);
}

/**Function*************************************************************
   Synopsis    []
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddCacheLookup(BddMan * p, int Arg1, int Arg2) {
  int * pEnt = p->pCache + 3*(BddHash(0, Arg1, Arg2) & p->nCacheMask);
  p->nCacheLookups++;
  return (pEnt[0] == Arg1 && pEnt[1] == Arg2) ? pEnt[2] : -1;
}
int BddCacheInsert(BddMan * p, int Arg1, int Arg2, int Res) {
  int * pEnt = p->pCache + 3*(BddHash(0, Arg1, Arg2) & p->nCacheMask);
  pEnt[0] = Arg1;  pEnt[1] = Arg2;  pEnt[2] = Res;
  p->nCacheMisses++;
  assert(Res >= 0);
  return Res;
}
void BddCacheClear(BddMan * p) {
  free(p->pCache);
  p->pCache = (int*)calloc(3*(p->nCacheMask + 1), sizeof(int));
}


/**Function*************************************************************
   Synopsis    []
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
BddMan * BddManAlloc(int nVars, int nPowTwo) {
  BddMan * p; int i;
  p = (BddMan*)calloc(1, sizeof(BddMan));
  p->nVars       = nVars;
  p->nObjsAlloc  = 1 << nPowTwo;
  p->nUniqueMask = (1 << nPowTwo) - 1;
  p->nCacheMask  = (1 << nPowTwo) - 1;
  p->nMinRemoved = p->nObjsAlloc;
  p->pUnique     = (int*)calloc(p->nUniqueMask + 1, sizeof(int));
  p->pNexts      = (int*)calloc(p->nObjsAlloc, sizeof(int));
  p->pCache      = (int*)calloc(3*(p->nCacheMask + 1), sizeof(int));
  p->pObjs       = (int*)calloc(2*p->nObjsAlloc, sizeof(int));
  p->pMark       = (unsigned char *)calloc(p->nObjsAlloc, sizeof(char));
  p->pRefs       = (unsigned short*)calloc(p->nObjsAlloc, sizeof(short));
  p->pVars       = (unsigned short*)calloc(p->nObjsAlloc, sizeof(short));
  p->pLevels     = (unsigned short*)calloc(p->nVars + 1, sizeof(short));
  for(i = 0; i < nVars + 1; i++)
    p->pLevels[i] = i;
  p->pVars[0]    = p->nVars;
  p->nObjs       = 1;
  for(i = 0; i < nVars; i++)
    BddUniqueCreate(p, i, 1, 0);
  assert(p->nObjs == nVars + 1);
  p->pEdges = NULL;
  return p;
}
void BddManFree(BddMan * p) {
  printf("BDD stats: Var = %d  Obj = %d  Alloc = %d  Hit = %d  Miss = %d\n", 
	  p->nVars, p->nObjs, p->nObjsAlloc, p->nCacheLookups-p->nCacheMisses, p->nCacheMisses);
  free(p->pUnique);
  free(p->pNexts);
  free(p->pCache);
  free(p->pObjs);
  free(p->pMark);
  free(p->pRefs);
  free(p->pVars);
  free(p->pLevels);
  free(p);
}

/**Function*************************************************************
   Synopsis    [Boolean AND.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddAnd(BddMan * p, int a, int b) {
  int v, r0, r1, r;
  if(a == 0) return 0;
  if(b == 0) return 0;
  if(a == 1) return b;
  if(b == 1) return a;
  if(a == b) return a;
  if(a > b)  return BddAnd(p, b, a);
  if((r = BddCacheLookup(p, a, b)) >= 0)
    return r;
  if(BddLevel(p, a) < BddLevel(p, b))
    v  = BddVar(p, a),
      r0 = BddAnd(p, BddElse(p, a), b), BddIncRef(p, r0),
      r1 = BddAnd(p, BddThen(p, a), b), BddIncRef(p, r1);
  else if(BddLevel(p, a) > BddLevel(p, b))
    v  = BddVar(p, b),
      r0 = BddAnd(p, a, BddElse(p, b)), BddIncRef(p, r0),
      r1 = BddAnd(p, a, BddThen(p, b)), BddIncRef(p, r1);
  else // if(BddVar(p, a) == BddVar(p, b))
    v  = BddVar(p, a),
      r0 = BddAnd(p, BddElse(p, a), BddElse(p, b)), BddIncRef(p, r0),
      r1 = BddAnd(p, BddThen(p, a), BddThen(p, b)), BddIncRef(p, r1);
  r = BddUniqueCreate(p, v, r1, r0);
  BddDecRef(p, r0), BddDecRef(p, r1);
  return BddCacheInsert(p, a, b, r);
}
int BddOr(BddMan * p, int a, int b) {
  return LitNot(BddAnd(p, LitNot(a), LitNot(b)));
}
int BddXor(BddMan * p, int a, int b) {
  int r0, r1, r;
  r0 = BddAnd(p, LitNot(a), b);
  BddIncRef(p, r0);
  r1 = BddAnd(p, a, LitNot(b));
  BddIncRef(p, r1);
  r = BddOr(p, r0, r1);
  BddDecRef(p, r0), BddDecRef(p, r1);
  return r;
}

/**Function*************************************************************
   Synopsis    [Counting nodes.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddCount_rec(BddMan * p, int i) {
  if(i < 2)
    return 0;
  if(BddMark(p, i))
    return 0;
  BddSetMark(p, i, 1);
  return 1 + BddCount_rec(p, BddElse(p, i)) + BddCount_rec(p, BddThen(p, i));
}
void BddUnmark_rec(BddMan * p, int i) {
  if(i < 2)
    return;
  if(!BddMark(p, i))
    return;
  BddSetMark(p, i, 0);
  BddUnmark_rec(p, BddElse(p, i));
  BddUnmark_rec(p, BddThen(p, i));
}
int BddCountNodes(BddMan * p, int i) {
  int Count = BddCount_rec(p, i);
  BddUnmark_rec(p, i);
  return Count;
}
int BddCountNodes(BddMan * p, int i, int j) {
  int Count = BddCount_rec(p, i);
  Count += BddCount_rec(p, j);
  BddUnmark_rec(p, i);
  BddUnmark_rec(p, j);
  return Count;
}

int BddCount_rec(BddMan * p, int i, std::vector<int> & v) {
  if(i < 2)
    return 0;
  if(BddMark(p, i))
    return 0;
  BddSetMark(p, i, 1);
  v[BddVar(p, i)]++;
  return 1 + BddCount_rec(p, BddElse(p, i), v) + BddCount_rec(p, BddThen(p, i), v);
}
int BddCountNodes(BddMan * p, int i, std::vector<int> & v) {
  int Count = BddCount_rec(p, i, v);
  BddUnmark_rec(p, i);
  return Count;
}

/**Function*************************************************************
   Synopsis    [Count ones]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddCountOnes_rec(BddMan * p, int x, std::string & s) {
  if(x == 1) {
    int idx = 0;
    for(int i = 0; i < s.size(); i++)
      if(s[i] == '-')
	idx++;
    return 1 << idx;
  }
  if(x == 0)
    return 0;
  int count = 0;
  s[BddVar(p, x)] = '1';
  count += BddCountOnes_rec(p, BddThen(p, x), s);
  s[BddVar(p, x)] = '0';
  count += BddCountOnes_rec(p, BddElse(p, x), s);
  s[BddVar(p, x)] = '-';
  return count;
}
int BddCountOnes(BddMan * p, int x) {
  std::string s;
  for(int i = 0; i < p->nVars; i++)
    s += "-";
  return BddCountOnes_rec(p, x, s);
}

double BddRatioOnes(BddMan * p, int x) {
  if(x == 1) return 1;
  if(x == 0) return 0;
  double count = 0;
  count += BddRatioOnes(p, BddThen(p, x));
  count += BddRatioOnes(p, BddElse(p, x));
  return count / 2;
}

/**Function*************************************************************
   Synopsis    [Garbage collection.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
void BddMark_rec(BddMan * p, int i) {
  if(i < 2)
    return;
  if(BddMark(p, i))
    return;
  BddSetMark(p, i, 1);
  BddMark_rec(p, BddElse(p, i));
  BddMark_rec(p, BddThen(p, i));
}
void BddDeregister(BddMan * p, int a) {
  int Var, Then, Else;
  Var = p->pVars[a], Then = p->pObjs[a+a], Else = p->pObjs[a+a+1];
  int *q = p->pUnique + (BddHash(Var, Then, Else) & p->nUniqueMask);
  for(; *q; q = p->pNexts + *q)
    if(*q == a) {
      *q = p->pNexts[*q];
      return;
    }
  abort();
}
void BddGarbageCollect(BddMan * p) {
  int count = 0;
  if(p->pEdges) { // during reorder
    // from list
    for(auto it = p->nodelist[p->reolowvar].begin(); it != p->nodelist[p->reolowvar].end();) {
      if(p->pEdges[*it] == 0) it = p->nodelist[p->reolowvar].erase(it);
      else it++;
    }
    // from table
    /* required for DC-symmetric
       for(int i = p->nVars + 1; i < p->nObjs; i++)
       if(p->pRefs[i] && !p->pEdges[i])
       BddMark_rec(p, Var2Lit(i, 0));
    */
    for(int i = p->nVars + 1; i < p->nObjs; i++) {
      //if(!p->pEdges[i] && !p->pMark[i]) {
      if(!p->pEdges[i]) {
	BddDeregister(p, i);
	p->pVars[i] = 0xffff;
	p->pNexts[i] = 0;
	count++;
	if(p->nMinRemoved > i) p->nMinRemoved = i;
      }
      /* required for DC-symmetric
	 for(int i = p->nVars + 1; i < p->nObjs; i++)
	 if(p->pRefs[i] && !p->pEdges[i])
	 BddUnmark_rec(p, Var2Lit(i, 0));
      */
    }
    std::cout << "delete " << count << std::endl;
    return;
  }
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    if(p->pRefs[i])
      BddMark_rec(p, Var2Lit(i, 0));
  for(int i = p->nVars + 1; i < p->nObjs; i++) {
    if(!p->pMark[i]) {
      BddDeregister(p, i);
      p->pVars[i] = 0xffff;
      p->pNexts[i] = 0;
      count++;
      if(p->nMinRemoved > i) p->nMinRemoved = i;
    }
  }
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    if(p->pRefs[i])
      BddUnmark_rec(p, Var2Lit(i, 0));
  std::cout << "delete " << count << std::endl;
  BddCacheClear(p);
}

/**Function*************************************************************
   Synopsis    [Swap levels at i and i + 1.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
void BddRecursiveRef(BddMan * p, int x) {
  if(x == 0 || x == 1) return;
  assert(!p->nodelist.empty());
  assert(p->pEdges);
  if(BddEdge(p, x) == 0) {
    p->nodelist[BddVar(p, x)].push_back(Lit2Var(x));
    BddRecursiveRef(p, BddThen(p, x));
    BddRecursiveRef(p, BddElse(p, x));
  }
  BddIncEdge(p, x);
}
void BddRecursiveDeref(BddMan * p, int x) {
  if(x == 0 || x == 1) return;
  assert(!p->nodelist.empty());
  assert(p->pEdges);
  BddDecEdge(p, x);
  if(BddEdge(p, x) == 0) {
    p->nodelist[BddVar(p, x)].remove(Lit2Var(x));
    BddRecursiveDeref(p, BddThen(p, x));
    BddRecursiveDeref(p, BddElse(p, x));
  }
}
int BddSwap(BddMan * p, int i) {
  assert(!p->nodelist.empty());
  assert(p->pEdges);
  int uv = BddLevel2Var(p, i);
  int lv = BddLevel2Var(p, i + 1);
  p->reolowvar = lv;
  int count = p->nodelist[uv].size() + p->nodelist[lv].size();
  // extract up nodes related to low nodes
  std::list<int> extracted;
  for(auto it = p->nodelist[uv].begin(); it != p->nodelist[uv].end();) {
    if(BddVar(p, p->pObjs[*it+*it]) == lv || BddVar(p, p->pObjs[*it+*it+1]) == lv) {
      extracted.push_back(*it);
      it = p->nodelist[uv].erase(it);
    }
    else it++;
  }
  // swap levels
  p->pLevels[uv] = i + 1;
  p->pLevels[lv] = i;
  // reconstruct extracted nodes
  for(auto a : extracted) {
    // get grandchildren with dec edges
    int t, e, tt, te, et, ee;
    t = p->pObjs[a+a], e = p->pObjs[a+a+1];
    if(BddVar(p, t) == lv) tt = BddThen(p, t), te = BddElse(p, t);
    else tt = te = t;
    if(BddVar(p, e) == lv) et = BddThen(p, e), ee = BddElse(p, e);
    else et = ee = e;
    // create new children with inc edges, and push them into list
    int nt, ne;
    if(tt == et) nt = tt;
    else {
      nt = BddUniqueCreate(p, uv, tt, et);
      if(BddEdge(p, nt) == 0)
	BddIncEdge(p, tt), BddIncEdge(p, et), p->nodelist[uv].push_back(Lit2Var(nt));
    }
    BddIncEdge(p, nt);
    if(ee == te) ne = ee;
    else {
      ne = BddUniqueCreate(p, uv, te, ee);
      if(BddEdge(p, ne) == 0)
	BddIncEdge(p, te), BddIncEdge(p, ee), p->nodelist[uv].push_back(Lit2Var(ne));
    }
    BddIncEdge(p, ne);
    BddDecEdge(p, t);
    if(BddVar(p, t) == lv && BddEdge(p, t) == 0) BddDecEdge(p, tt), BddDecEdge(p, te);
    BddDecEdge(p, e);
    if(BddVar(p, e) == lv && BddEdge(p, e) == 0) BddDecEdge(p, et), BddDecEdge(p, ee);
    // reregister the new node with new children, and push it into list
    BddDeregister(p, a);
    int Var, Then, Else;
    Var = lv, Then = nt, Else = ne;
    assert(Then != Else);
    assert(!LitIsCompl(Else));
    int *q = p->pUnique + (BddHash(Var, Then, Else) & p->nUniqueMask);
    p->pNexts[a] = *q;
    *q = a;
    p->pVars[*q] = Var;
    p->pObjs[*q+*q] = Then;
    p->pObjs[*q+*q+1] = Else;
    p->nodelist[lv].push_back(a);
  }
  // erase zero edge nodes
  for(auto it = p->nodelist[lv].begin(); it != p->nodelist[lv].end();) {
    if(p->pEdges[*it] == 0) it = p->nodelist[lv].erase(it);
    else it++;
  }
  return p->nodelist[uv].size() + p->nodelist[lv].size() - count;
}
void BddSiftReorder(BddMan * p, double maxinc = 1.1) {
  bool freoverbose = 0;
  // allocation
  p->pEdges = (unsigned*)calloc(p->nObjsAlloc, sizeof(int));
  p->nodelist.resize(p->nVars);
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    if(p->pRefs[i])
      BddRecursiveRef(p, Var2Lit(i, 0));
  // count nodes and decide order to sift
  int basecount = 0;
  std::vector<int> dorder;
  {
    // count nodes
    for(int i = 0; i < p->nVars; i++)
      basecount += p->nodelist[i].size();
    // decide order
    std::vector<bool> done(p->nVars);
    while(1) {
      int maxnodes = 0;
      int v = -1;
      for(int i = 0; i < p->nVars; i++) {
	if(done[i]) continue;
	if(maxnodes < p->nodelist[i].size())
	  maxnodes = p->nodelist[i].size(), v = i;
      }
      if(v == -1) break;
      dorder.push_back(v);
      done[v] = 1;
    }
  }
  // sift
  int ndiff = 0;
  for(int v : dorder) {
    if(freoverbose) std::cout << "sift " << v << std::endl;
    int mindiff = ndiff;
    int minlevel = BddVar2Level(p, v);
    if(freoverbose) std::cout << "\tlevel " << BddVar2Level(p, v) << " nodes " << basecount + ndiff << std::endl;
    bool godown = BddVar2Level(p, v) >= (p->nVars >> 1);
    int nite = 0;
    while(1) {
      while((godown && BddVar2Level(p, v) < p->nVars - 1) ||
	    (!godown && BddVar2Level(p, v) > 0)) {
	if(godown) ndiff += BddSwap(p, BddVar2Level(p, v));
	else ndiff += BddSwap(p, BddVar2Level(p, v) - 1);
	if(freoverbose) std::cout << "\tlevel " << BddVar2Level(p, v) << " nodes " << basecount + ndiff << std::endl;
	if(nite == 2) {
	  if(BddVar2Level(p, v) == minlevel) break;
	  continue;
	}
	if(basecount * (maxinc - 1) < ndiff) break;
	if(mindiff >= ndiff)
	  mindiff = ndiff, minlevel = BddVar2Level(p, v);
      }
      godown ^= 1;
      if(nite == 2) break;
      nite++;
      if(nite == 2 && BddVar2Level(p, v) == minlevel) break;
    }
  }
  // verify
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    if(p->pRefs[i])
      BddRecursiveDeref(p, Var2Lit(i, 0));
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    assert(p->pEdges[i] == 0);
  // finalize
  free(p->pEdges);
  p->pEdges = NULL;
  p->nodelist.clear();
  BddCacheClear(p);
}  

/**Function*************************************************************
   Synopsis    [symmetric.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
bool BddCheckSymmetric(BddMan * p, int i) {
  assert(!p->nodelist.empty());
  assert(p->pEdges);
  int uv = BddLevel2Var(p, i);
  int lv = BddLevel2Var(p, i + 1);
  int count = 0;
  // check function
  for(int a : p->nodelist[uv]) {
    int t, e, te, et;
    t = p->pObjs[a+a], e = p->pObjs[a+a+1];
    if(BddVar(p, t) == lv) te = BddElse(p, t), count++;
    else te = t;
    if(BddVar(p, e) == lv) et = BddThen(p, e), count++;
    else et = e;
    if(te != et) return 0;
  }
  // check edges
  for(int a : p->nodelist[lv])
    count -= p->pEdges[a];
  if(count != 0) return 0;
  return 1;
}
void BddSymmetricTest(BddMan * p, int x) {
  p->pEdges = (unsigned*)calloc(p->nObjsAlloc, sizeof(int));
  p->nodelist.resize(p->nVars);
  BddRecursiveRef(p, x);

  for(int i = 0; i < p->nVars - 1; i++) {
    std::cout << "level " << i << std::endl;
    if(BddCheckSymmetric(p, i))
      std::cout << "symmetric at level " << i << " var " << BddLevel2Var(p, i) << " and " << BddLevel2Var(p, i+1) << std::endl;
    std::cout << std::endl;
  }
  
  free(p->pEdges);
  p->pEdges = NULL;
  p->nodelist.clear();
}
void BddSymmetricSiftReorder(BddMan * p, double maxinc = 1.1) {
  bool freoverbose = 1;
  // allocation
  p->pEdges = (unsigned*)calloc(p->nObjsAlloc, sizeof(int));
  p->nodelist.resize(p->nVars);
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    if(p->pRefs[i])
      BddRecursiveRef(p, Var2Lit(i, 0));
  // get current symmetry
  std::vector<int> group(p->nVars);
  for(int i = 0; i < p->nVars; i++)
    group[i] = i;
  for(int i = 0; i < p->nVars - 1; i++) {
    if(BddCheckSymmetric(p, i)) {
      group[BddLevel2Var(p, i + 1)] = group[BddLevel2Var(p, i)];
      if(freoverbose) std::cout << "symmetric at level " << i << " var " << BddLevel2Var(p, i) << " and " << BddLevel2Var(p, i + 1) << std::endl;
    }
  }
  std::vector<int> groupheads(p->nVars);
  std::vector<int> groupsizes(p->nVars);
  for(int i = 0; i < p->nVars; i++)
    groupheads[i] = -1;
  for(int i = 0; i < p->nVars; i++) {
    int j = BddLevel2Var(p, i);
    groupsizes[group[j]]++;
    if(groupheads[group[j]] == -1)
      groupheads[group[j]] = j;
  }
  if(freoverbose) {
    for(int i = 0; i < p->nVars; i++) {
      if(groupheads[i] == -1) continue;
      std::cout << "group " << i << " head " << groupheads[i] << " size " << groupsizes[i] << std::endl;
    }
  }
  // count nodes and decide order to sift
  int basecount = 0;
  std::vector<int> dorder;
  {
    // count nodes
    for(int i = 0; i < p->nVars; i++)
      basecount += p->nodelist[i].size();
    // decide order
    std::vector<bool> done(p->nVars);
    while(1) {
      int maxnodes = 0;
      int v = -1;
      for(int i = 0; i < p->nVars; i++) {
	if(done[i]) continue;
	if(maxnodes < p->nodelist[i].size())
	  maxnodes = p->nodelist[i].size(), v = i;
      }
      if(v == -1) break;
      dorder.push_back(v);
      for(int i = 0; i < p->nVars; i++)
 	if(group[i] == group[v])
 	  done[i] = 1;
    }
  }
  // sift
  int ndiff = 0;
  std::vector<bool> done(p->nVars);
  for(int v : dorder) {
    v = groupheads[group[v]];
    if(done[v]) continue;
    if(freoverbose) std::cout << "sift " << v << " groupsize " << groupsizes[group[v]] << std::endl;
    int mindiff = ndiff;
    int minlevel = BddVar2Level(p, v);
    if(freoverbose) std::cout << "\tlevel " << BddVar2Level(p, v) << " nodes " << basecount + ndiff << std::endl;
    bool godown = BddVar2Level(p, v) >= (p->nVars >> 1);
    int nite = 0;
    while(1) {
      while((godown && BddVar2Level(p, v) + groupsizes[group[v]] < p->nVars) ||
	    (!godown && BddVar2Level(p, v) > 0)) {
	if(godown) {
	  int nlev = BddVar2Level(p, v) + groupsizes[group[v]];
	  int nsize = groupsizes[group[BddLevel2Var(p, nlev)]];
	  for(int k = 0; k < nsize; k++)
	    for(int i = groupsizes[group[v]] - 1; i >= 0; i--)
	      ndiff += BddSwap(p, BddVar2Level(p, v) + i);
	}
	else {
	  int nlev = BddVar2Level(p, v) - 1;
	  int nsize = groupsizes[group[BddLevel2Var(p, nlev)]];
	  for(int k = 0; k < nsize; k++) {
	    int j = BddVar2Level(p, v);
	    for(int i = 0; i < groupsizes[group[v]]; i++)
	      ndiff += BddSwap(p, j + i - 1);
	  }
	}
	if(freoverbose) std::cout << "\tlevel " << BddVar2Level(p, v) << " nodes " << basecount + ndiff << std::endl;
	// check symmetric
	int nlev = BddVar2Level(p, v) + groupsizes[group[v]];
 	if(nlev != p->nVars && BddCheckSymmetric(p, nlev - 1)) {
 	  if(freoverbose) std::cout << "found symmetric with var ";
 	  int j = group[BddLevel2Var(p, nlev)];
 	  for(int i = 0; i < p->nVars; i++)
 	    if(group[i] == j) {
 	      if(freoverbose) std::cout << i << ", ";
 	      group[i] = group[v];
 	      groupsizes[group[v]]++;
 	    }
 	  if(freoverbose) std::cout << std::endl;
 	  // reset min
 	  mindiff = ndiff;
 	  minlevel = BddVar2Level(p, v);
	  nite = 0;
 	}
	if(nite == 2) {
	  if(BddVar2Level(p, v) == minlevel) break;
	  continue;
	}
	if(basecount * (maxinc - 1) < ndiff) break;
	if(mindiff >= ndiff)
	  mindiff = ndiff, minlevel = BddVar2Level(p, v);
      }
      godown ^= 1;
      if(nite == 2) break;
      nite++;
      if(nite == 2 && BddVar2Level(p, v) == minlevel) break;
    }
    done[v] = 1;
  }
  // verify
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    if(p->pRefs[i])
      BddRecursiveDeref(p, Var2Lit(i, 0));
  for(int i = p->nVars + 1; i < p->nObjs; i++)
    assert(p->pEdges[i] == 0);
  // finalize
  free(p->pEdges);
  p->pEdges = NULL;
  p->nodelist.clear();
  BddCacheClear(p);
}

/**Function*************************************************************
   Synopsis    [DC-symmetric.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddUniv(BddMan * p, int f, int v) {
  if(f == 0 || f == 1) return f;
  if(BddVar(p, f) == v)
    return BddAnd(p, BddElse(p, f), BddThen(p, f));
  int r0, r1, r;
  r0 = BddUniv(p, BddElse(p, f), v), BddIncRef(p, r0);
  r1 = BddUniv(p, BddThen(p, f), v), BddIncRef(p, r1);
  r = BddUniqueCreate(p, BddVar(p, f), r1, r0);
  BddDecRef(p, r0), BddDecRef(p, r1);
  return r;
}
void BddRecursivePNRef(BddMan * p, int x) {
  if(x == 0 || x == 1) return;
  assert(!p->nodelist.empty());
  assert(p->pEdges);
  if(BddEdge(p, x) == 0)
    p->nodelist[BddVar(p, x)].push_back(Lit2Var(x));
  if(LitIsCompl(x)) {
    if(BddNEdge(p, x) == 0)
      BddRecursivePNRef(p, BddThen(p, x)), BddRecursivePNRef(p, BddElse(p, x));
    BddIncNEdge(p, x);
  }
  else {
    if(BddPEdge(p, x) == 0)
      BddRecursivePNRef(p, BddThen(p, x)), BddRecursivePNRef(p, BddElse(p, x));
    BddIncPEdge(p, x);
  }
}
bool BddCheckDCSymmetric(BddMan * p, int i) {
  // assume 0 is DC
  assert(!p->nodelist.empty());
  assert(p->pEdges);
  int uv = BddLevel2Var(p, i);
  int lv = BddLevel2Var(p, i + 1);
  std::map<int, unsigned> count;
  // check function
  for(int a : p->nodelist[uv]) {
    int t, e, te, et;
    t = p->pObjs[a+a], e = p->pObjs[a+a+1];
    //std::cout << "\t" << a << " edge " << (p->pEdges[a] & 0xffff) << " " << (p->pEdges[a] >> 16) << " then " << t << "(" << BddVar(p, t) << ") else " << e << "(" << BddVar(p, e) << ")" << std::endl;
    for(int m = 0; m <= 1; m++) {
      if(!m && !(p->pEdges[a] & 0xffff)) continue;
      if(m && !(p->pEdges[a] >> 16)) continue;
      if(BddVar(p, t) == lv) count[Lit2Var(t)] += (m ^ LitIsCompl(t))? 0x10000: 1;
      if(BddVar(p, e) == lv) count[Lit2Var(e)] += (m ^ LitIsCompl(e))? 0x10000: 1;
      if(m) // negated case
	t = LitNot(t), e = LitNot(e);
      if(t == 0 || e == 0) continue;
      if(BddVar(p, t) == lv) te = BddElse(p, t);
      else te = t;
      if(BddVar(p, e) == lv) et = BddThen(p, e);
      else et = e;
      if(te == 0 || et == 0) continue;
      int r, c;
      r = BddOr(p, te, et);
      BddIncRef(p, r);
      c = BddUniv(p, r, p->nVars - 1);
      BddDecRef(p, r);
      if(c != 0) {
	std::cout << "inconsistent when " << c << std::endl;
	return 0;
      }
      //std::cout << "\t\torg " << BddCountNodes(p, te, et) << " new " << BddCountNodes(p, r) << std::endl;
    }
  }
  // check edges
  for(int a : p->nodelist[lv]) {
    unsigned d = p->pEdges[a] - count[a];
    if(d == 0) continue;
    std::cout << "\t\textra check" << std::endl;
    int t, e;
    t = p->pObjs[a+a], e = p->pObjs[a+a+1];
    for(int m = 0; m <= 1; m++) {
      if(!m && !(d & 0xffff)) continue;
      if(m && !(d >> 16)) continue;
      if(m) // negated case
	t = LitNot(t), e = LitNot(e);
      int r, c;
      r = BddOr(p, t, e);
      BddIncRef(p, r);
      c = BddUniv(p, r, p->nVars - 1);
      BddDecRef(p, r);
      if(c != 0) {
	std::cout << "inconsistent when " << c << std::endl;
	return 0;
      }
    }
  }
  return 1;
}
void BddPrint(BddMan * p, int a);
void BddDCSymmetricTest(BddMan * p, int x) {
  p->pEdges = (unsigned*)calloc(p->nObjsAlloc, sizeof(int));
  p->nodelist.resize(p->nVars);
  BddRecursivePNRef(p, x);
  /*
    for(int i = 0; i < p->nVars - 2; i++) { // assume the last variable is the output value
    std::cout << "level" << i << std::endl;
    for(int a : p->nodelist[i]) {
    int t, e;
    t = p->pObjs[a+a], e = p->pObjs[a+a+1];
    std::cout << "\t" << a << " edge " << (p->pEdges[a] & 0xffff) << " " << (p->pEdges[a] >> 16) << " then " << t << "(" << BddVar(p, t) << ") else " << e << "(" << BddVar(p, e) << ")" << std::endl;
    }
    }
  */
  for(int i = 0; i < p->nVars - 2; i++) { // assume the last variable is the output value
    std::cout << "level" << i << std::endl;
    if(BddCheckDCSymmetric(p, i))
      std::cout << "DC-symmetric at level " << i << " var " << BddLevel2Var(p, i) << " and " << BddLevel2Var(p, i+1) << std::endl;
    std::cout << std::endl;
  }
  
  free(p->pEdges);
  p->pEdges = NULL;
  p->nodelist.clear();
}


/**Function*************************************************************
   Synopsis    [Printing BDD.]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
void BddPrint_rec(BddMan * p, int a, int * pPath) {
  if(a == 0) 
    return;
  if(a == 1) { 
    int i;
    for(i = 0; i < p->nVars; i++)
      if(pPath[i] == 0 || pPath[i] == 1)
	printf("%c%d", pPath[i] ? '+' : '-', i);
    printf(" ");
    return; 
  }
  pPath[BddVar(p, a)] =  0;
  BddPrint_rec(p, BddElse(p, a), pPath);
  pPath[BddVar(p, a)] =  1;
  BddPrint_rec(p, BddThen(p, a), pPath);
  pPath[BddVar(p, a)] = -1;
}
void BddPrint(BddMan * p, int a) {
  int * pPath = (int*)calloc(p->nVars, sizeof(int));
  printf("BDD %d = ", a);
  BddPrint_rec(p, a, pPath);
  free(pPath);
  printf("\n");
}
void BddPrintTest(BddMan * p) {
  int bVarA = BddIthVar(0);
  int bVarB = BddIthVar(1);
  int bVarC = BddIthVar(2);
  int bVarD = BddIthVar(3);
  int bAndAB = BddAnd(p, bVarA, bVarB);
  int bAndCD = BddAnd(p, bVarC, bVarD);
  int bFunc  = BddOr(p, bAndAB, bAndCD);
  BddPrint(p, bFunc);
  printf("Nodes = %d\n", BddCountNodes(p, bFunc));
}

/**Function*************************************************************
   Synopsis    [bdd2aig]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int GenAig_rec(BddMan * man, aigman * aig, std::map<int, int> & m, int x) {
  if(x == 0)
    return 0;
  if(x == 1)
    return 1;
  if(LitIsCompl(x))
    return GenAig_rec(man, aig, m, LitNot(x)) ^ 1;
  if(m.count(x))
    return m[x];
  int c = (BddVar(man, x) + 1) << 1;
  int f1 = GenAig_rec(man, aig, m, BddThen(man, x));
  int f0 = GenAig_rec(man, aig, m, BddElse(man, x));
  int f = aig->newite(c, f1, f0);
  m[x] = f;
  return f;
}

aigman *GenAig(BddMan * man, int x, int nVars = -1) {
  if(nVars == -1) nVars = man->nVars;
  aigman *p = new aigman(nVars);
  std::map<int, int> m;
  int f = GenAig_rec(man, p, m, x);
  p->newpo(f);
  return p;
}

/**Function*************************************************************
   Synopsis    [traditional reduction using care-set]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddRestrict(BddMan * p, int f, int c) {
  assert(c);
  int r0, r1, r;
  if(c == 1) return f;
  if(f == 0 || f == 1) return f;
  if(!BddElse(p, c)) return BddRestrict(p, f, BddThen(p, c));
  if(!BddThen(p, c)) return BddRestrict(p, f, BddElse(p, c));
  if(BddLevel(p, f) > BddLevel(p, c))
    return BddRestrict(p, f, BddOr(p, BddElse(p, c), BddThen(p, c)));
  if(BddLevel(p, f) < BddLevel(p, c))
    r0 = BddRestrict(p, BddElse(p, f), c), BddIncRef(p, r0),
      r1 = BddRestrict(p, BddThen(p, f), c), BddIncRef(p, r1);
  else
    r0 = BddRestrict(p, BddElse(p, f), BddElse(p, c)), BddIncRef(p, r0),
      r1 = BddRestrict(p, BddThen(p, f), BddThen(p, c)), BddIncRef(p, r1);
  r = BddUniqueCreate(p, BddVar(p, f), r1, r0);
  BddDecRef(p, r0), BddDecRef(p, r1);
  return r;
}

/**Function*************************************************************
   Synopsis    [traditional squeeze between l (lower) and u (upper) bound]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
int BddSqueeze(BddMan * p, int l, int u, bool finter = 1, bool fhigheffort = 0) {
  if(l == 0) return l;
  if(u == 1) return u;
  int topu, topl, index, le, lt, ue, ut;
  topu = BddLevel(p, u);
  topl = BddLevel(p, l);
  if(topu <= topl) index = BddVar(p, u), ut = BddThen(p, u), ue = BddElse(p, u);
  else index = BddVar(p, l), ut = ue = u;
  if(topl <= topu) lt = BddThen(p, l), le = BddElse(p, l);
  else lt = le = l;
  int r, tmp;
  if(BddOr(p, LitNot(lt), le) == 1 && BddOr(p, LitNot(ue), ut) == 1)
    return BddSqueeze(p, le, ue, finter, fhigheffort);
  if(BddOr(p, LitNot(le), lt) == 1 && BddOr(p, LitNot(ut), ue) == 1)
    return BddSqueeze(p, lt, ut, finter, fhigheffort);
  if(finter) {
    if(BddOr(p, LitNot(le), LitNot(ut)) == 1 && BddOr(p, ue, lt) == 1) {
      tmp = BddSqueeze(p, lt, ut, finter, fhigheffort);
      BddIncRef(p, tmp);
      r = BddUniqueCreate(p, index, tmp, LitNot(tmp));
      BddDecRef(p, tmp);
      return r;
    }
    if(BddOr(p, LitNot(lt), LitNot(ue)) == 1 && BddOr(p, ut, le) == 1) {
      tmp = BddSqueeze(p, le, ue, finter, fhigheffort);
      BddIncRef(p, tmp);
      r = BddUniqueCreate(p, index, LitNot(tmp), tmp);
      BddDecRef(p, tmp);
      return r;
    }
  }
  int ar = -1;
  if(fhigheffort && BddOr(p, LitNot(lt), ue) == 1 && BddOr(p, LitNot(le), ut) == 1) {
    int au, al;
    au = BddAnd(p, ut, ue);
    BddIncRef(p, au);
    al = BddOr(p , lt, le);
    BddIncRef(p, al);
    ar = BddSqueeze(p, al, au, finter, fhigheffort);
    BddIncRef(p, ar);
    BddDecRef(p, au), BddDecRef(p, al);
  }
  int t, e;
  t = BddSqueeze(p, lt, ut, finter, fhigheffort);
  BddIncRef(p, t);
  e = BddSqueeze(p, le, ue, finter, fhigheffort);
  BddIncRef(p, e);
  r = (t == e) ? t : BddUniqueCreate(p, index, t, e);
  BddDecRef(p, t), BddDecRef(p, e);
  if(ar != -1) {
    if(BddCountNodes(p, ar) <= BddCountNodes(p, r))
      r = ar;
    BddDecRef(p, ar);
  }
  return r;
}

/**Function*************************************************************
   Synopsis    [minimize with DC]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
bool BddCheckIntersect(BddMan * p, int af, int ag, int bf, int bg) {
  // terminal (care set)
  if(ag == 0 && bg == 0) return af == bf;
  // terminal (DC)
  assert(!(ag == 1 && bg == 1));
  if(ag == 1) return 1;
  if(bg == 1) return 1;
  // top var
  int l = std::min({BddLevel(p, af), BddLevel(p, ag), BddLevel(p, bf), BddLevel(p, bg)});
  int af0, af1, ag0, ag1, bf0, bf1, bg0, bg1;
  if(l == BddLevel(p, af)) af0 = BddElse(p, af), af1 = BddThen(p, af);
  else af0 = af1 = af;
  if(l == BddLevel(p, ag)) ag0 = BddElse(p, ag), ag1 = BddThen(p, ag);
  else ag0 = ag1 = ag;
  if(l == BddLevel(p, bf)) bf0 = BddElse(p, bf), bf1 = BddThen(p, bf);
  else bf0 = bf1 = bf;
  if(l == BddLevel(p, bg)) bg0 = BddElse(p, bg), bg1 = BddThen(p, bg);
  else bg0 = bg1 = bg;
  // only one case is cared
  if(ag0 == 1 && bg0 == 1)
    return BddCheckIntersect(p, af1, ag1, bf1, bg1);
  if(ag1 == 1 && bg1 == 1)
    return BddCheckIntersect(p, af0, ag0, bf0, bg0);
  // recurse for each case
  bool r0, r1;
  r0 = BddCheckIntersect(p, af0, ag0, bf0, bg0);
  if(!r0) return 0;
  r1 = BddCheckIntersect(p, af1, ag1, bf1, bg1);
  return r0 && r1;
}
int BddDCIntersect2(BddMan * p, int af, int ag, int bf, int bg) {
  // terminal (care set)
  if(ag == 0 && bg == 0) assert(af == bf);
  if(ag == 0) return af;
  if(bg == 0) return bf;
  // terminal (DC)
  assert(!(ag == 1 && bg == 1));
  if(ag == 1) return bf;
  if(bg == 1) return af;
  // top var
  int l = std::min({BddLevel(p, af), BddLevel(p, ag), BddLevel(p, bf), BddLevel(p, bg)});
  int v, af0, af1, ag0, ag1, bf0, bf1, bg0, bg1;
  if(l == BddLevel(p, af)) v = BddVar(p, af), af0 = BddElse(p, af), af1 = BddThen(p, af);
  else af0 = af1 = af;
  if(l == BddLevel(p, ag)) v = BddVar(p, ag), ag0 = BddElse(p, ag), ag1 = BddThen(p, ag);
  else ag0 = ag1 = ag;
  if(l == BddLevel(p, bf)) v = BddVar(p, bf), bf0 = BddElse(p, bf), bf1 = BddThen(p, bf);
  else bf0 = bf1 = bf;
  if(l == BddLevel(p, bg)) v = BddVar(p, bg), bg0 = BddElse(p, bg), bg1 = BddThen(p, bg);
  else bg0 = bg1 = bg;
  // only one case is cared
  if(ag0 == 1 && bg0 == 1)
    return BddDCIntersect2(p, af1, ag1, bf1, bg1);
  if(ag1 == 1 && bg1 == 1)
    return BddDCIntersect2(p, af0, ag0, bf0, bg0);
  // recurse for each case
  int r0, r1, r;
  r0 = BddDCIntersect2(p, af0, ag0, bf0, bg0);
  BddIncRef(p, r0);
  r1 = BddDCIntersect2(p, af1, ag1, bf1, bg1);
  BddIncRef(p, r1);
  r = BddUniqueCreate(p, v, r1, r0);
  BddDecRef(p, r0), BddDecRef(p, r1);
  return r;
}
int BddMinimize3(BddMan * p, int f, int g, bool finter = 1) {
  // terminal (care set)
  if(g == 0) return f;
  assert(g != 1);
  // top var
  if(BddLevel(p, f) > BddLevel(p, g)) {
    int t, r;
    t = BddAnd(p, BddElse(p, g), BddThen(p, g));
    BddIncRef(p, t);
    r = BddMinimize3(p, f, t, finter);
    BddDecRef(p, t);
    return r;
  }
  int var = BddVar(p, f);
  int f0, f1, g0, g1;
  f0 = BddElse(p, f), f1 = BddThen(p, f);
  if(var == BddVar(p, g)) g0 = BddElse(p, g), g1 = BddThen(p, g);
  else g0 = g1 = g;
  // only one case is cared
  if(g0 == 1)
    return BddMinimize3(p, f1, g1, finter);
  if(g1 == 1)
    return BddMinimize3(p, f0, g0, finter);
  // check if intersection exists
  if(finter) {
    if(f0 != f1) {
      if(BddCheckIntersect(p, f0, g0, f1, g1)) {
	int f2, g2, r;
	f2 = BddDCIntersect2(p, f0, g0, f1, g1);
	BddIncRef(p, f2);
	g2 = BddAnd(p, g0, g1);
	BddIncRef(p, g2);
	r = BddMinimize3(p, f2, g2, finter);
	BddDecRef(p, f2), BddDecRef(p, g2);
	return r;
      }
      if(BddCheckIntersect(p, LitNot(f0), g0, f1, g1)) {
	int f2, g2, t, r;
	f2 = BddDCIntersect2(p, LitNot(f0), g0, f1, g1);
	BddIncRef(p, f2);
	g2 = BddAnd(p, g0, g1);
	BddIncRef(p, g2);
	t = BddMinimize3(p, f2, g2, finter);
	BddIncRef(p, t);
	BddDecRef(p, f2), BddDecRef(p, g2);
	r = BddUniqueCreate(p, var, t, LitNot(t));
	BddDecRef(p, t);
	return r;
      }
    }
  }
  // recurse for each case
  int r0, r1, r;
  r0 = BddMinimize3(p, f0, g0, finter);
  BddIncRef(p, r0);
  r1 = BddMinimize3(p, f1, g1, finter);
  BddIncRef(p, r1);
  r = BddUniqueCreate(p, var, r1, r0);
  BddDecRef(p, r0), BddDecRef(p, r1);
  return r;
}
/**Function*************************************************************
   Synopsis    [minimize with DC]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
void BddMinimizeLevel(BddMan * p, std::vector<std::pair<int, int> > & ts, std::map<std::pair<int, int>, std::pair<std::pair<int, int>, bool> > & m, double maxinc = 1.1) {
  bool fverbose = 0;
  std::vector<std::pair<int, int> > tsold = ts;
  std::vector<int> c(ts.size());
  for(int i = 0; i < ts.size(); i++)
    c[i] = i + 1;
  // compare one (const)
  for(int i = 0; i < ts.size(); i++) {
    if(BddOr(p, ts[i].first, ts[i].second) == 1) {
      if(fverbose) std::cout << "\t\tassign " << i << " to 1 " << std::endl;
      BddDecRef(p, ts[i].first), BddDecRef(p, ts[i].second);
      ts[i].first = 1;
      ts[i].second = 0;
      m[tsold[i]] = std::make_pair(ts[i], 0);
      c[i] = 0;
      continue;
    }
    if(BddOr(p, LitNot(ts[i].first), ts[i].second) == 1) {
      if(fverbose) std::cout << "\t\tassign " << i << " to 0 " << std::endl;
      BddDecRef(p, ts[i].first), BddDecRef(p, ts[i].second);
      ts[i].first = 0;
      ts[i].second = 0;
      m[tsold[i]] = std::make_pair(ts[i], 0);
      c[i] = 0;
      continue;
    }
  }
  // compare two (intersect)
  for(int i = 0; i < ts.size() - 1; i++) {
    if(abs(c[i]) <= i) continue;
    for(int j = i + 1; j < ts.size(); j++) {
      if(abs(c[j]) <= j) continue;
      int prev = BddCountNodes(p, ts[i].first, ts[j].first);
      if(BddCheckIntersect(p, ts[i].first, ts[i].second, ts[j].first, ts[j].second)) {
	int f2 = BddDCIntersect2(p, ts[i].first, ts[i].second, ts[j].first, ts[j].second);
	int next = BddCountNodes(p, f2);
	if(next < prev * maxinc) {
	  if(fverbose) std::cout << "\t\tbuf merge " << i << " " << j << "(" << prev << "->" << next << ")" << std::endl;
	  BddIncRef(p, f2);
	  int g2 = BddAnd(p, ts[i].second, ts[j].second);
	  BddIncRef(p, g2);
	  BddDecRef(p, ts[i].first), BddDecRef(p, ts[i].second);
	  ts[i].first = f2;
	  ts[i].second = g2;
	  m[tsold[i]] = std::make_pair(ts[i], 0);
	  c[j] = i + 1;
	  continue;
	}
      }
      if(BddCheckIntersect(p, ts[i].first, ts[i].second, LitNot(ts[j].first), ts[j].second)) {
	int f2 = BddDCIntersect2(p, ts[i].first, ts[i].second, LitNot(ts[j].first), ts[j].second);
	int next = BddCountNodes(p, f2);
	if(next < prev * maxinc) {
	  if(fverbose) std::cout << "\t\txor merge " << i << " " << j << "(" << prev << "->" << next << ")" << std::endl;
	  BddIncRef(p, f2);
	  int g2 = BddAnd(p, ts[i].second, ts[j].second);
	  BddIncRef(p, g2);
	  BddDecRef(p, ts[i].first), BddDecRef(p, ts[i].second);
	  ts[i].first = f2;
	  ts[i].second = g2;
	  m[tsold[i]] = std::make_pair(ts[i], 0);
	  c[j] = -(i + 1);
	  continue;
	}
      }
    }
  }
  // map registeration, replace by new nodes
  std::vector<std::pair<int, int> > tsnew;
  for(int i = 0; i < ts.size(); i++) {
    if(c[i] == i + 1)
      tsnew.push_back(ts[i]);
    else if(c[i] != 0) {
      BddDecRef(p, ts[i].first), BddDecRef(p, ts[i].second);
      m[tsold[i]] = std::make_pair(ts[abs(c[i]) - 1], c[i] < 0);
    }
  }
  ts = tsnew;
}
int BddMinimizeLevelTD(BddMan * p, int f, int g) {
  bool fverbose = 0;
  std::set<std::pair<int, int> > fronts;
  std::map<std::pair<int, int>, std::pair<std::pair<int, int>, bool> > m;
  std::map<std::pair<int, int>, std::pair<std::pair<int, int>, std::pair<int, int> > > cs;
  std::vector<std::pair<int, int> > res;
  BddIncRef(p, f), BddIncRef(p, g);
  std::pair<int, int> root(f, g);
  fronts.insert(root);
  // minimize top down
  for(int i = 0; i < p->nVars; i++) {
    if(fverbose) std::cout << "level " << i << std::endl;
    // get nodes in the level
    std::vector<std::pair<int, int> > targets;
    std::vector<std::pair<int, int> > nfronts;
    for(auto it = fronts.begin(); it != fronts.end();) {
      if(BddLevel(p, it->first) == i) {
	targets.push_back(*it);
	it = fronts.erase(it);
      }
      else if(BddLevel(p, it->second) == i) {
        int t = BddAnd(p, BddElse(p, it->second), BddThen(p, it->second));
	BddIncRef(p, t);
	BddDecRef(p, it->second);
	nfronts.push_back(std::make_pair(it->first, t));
	it = fronts.erase(it);
      }
      else ++it;
    }
    for(auto t : nfronts) {
      if(fronts.count(t)) BddDecRef(p, t.first), BddDecRef(p, t.second);
      else fronts.insert(t);
    }
    if(fverbose) {
      std::cout << "\ttargets " << targets.size() << std::endl;
      int j = 0;
      for(auto t : targets) {
	std::cout << "\t\tnode" << j++ << " " << t.first << "," << t.second;
	std::cout << " (" << BddElse(p, t.first) << "," << BddElse(p, t.second) << " " << BddThen(p, t.first) << "," << BddThen(p, t.second) << ")";
	std::cout << std::endl;
      }
    }
    // minimize the level
    if(targets.size() > 1) {
      if(fverbose) std::cout << "\tminimize" << std::endl;
      BddMinimizeLevel(p, targets, m);
    }
    if(fverbose) {
      std::cout << "\tres " << targets.size() << std::endl;
      int j = 0;
      for(auto t : targets) {
	std::cout << "\t\tnode" << j++ << " " << t.first << "," << t.second;
	std::cout << " (" << BddElse(p, t.first) << "," << BddElse(p, t.second) << " " << BddThen(p, t.first) << "," << BddThen(p, t.second) << ")";
	std::cout << std::endl;
      }
    }
    // add children to fronts, add targets to res
    for(auto t : targets) {
      assert(t.second != 1);
      assert(t.first != 0 && t.first != 1);
      int t0f, t0g, t1f, t1g;
      if(BddLevel(p, t.first) == i) t0f = BddElse(p, t.first), t1f = BddThen(p, t.first);
      else t0f = t1f = t.first;
      if(BddLevel(p, t.second) == i) t0g = BddElse(p, t.second), t1g = BddThen(p, t.second);
      else t0g = t1g = t.second;
      std::pair<int, int> t0, t1;
      t0 = std::make_pair(t0f, t0g);
      t1 = std::make_pair(t1f, t1g);
      cs[t] = std::make_pair(t0, t1);
      assert(t0g != 1 || t1g != 1);
      if(t0g != 1 && t0f != 0 && t0f != 1 && !fronts.count(t0))
	fronts.insert(t0), BddIncRef(p, t0f), BddIncRef(p, t0g);
      if(t1g != 1 && t1f != 0 && t1f != 1 && !fronts.count(t1))
	fronts.insert(t1), BddIncRef(p, t1f), BddIncRef(p, t1g);
      res.push_back(t);
    }
  }
  // construct bottom up
  std::reverse(res.begin(), res.end());
  for(auto t : res) {
    // get previous children
    int l = std::min(BddLevel(p, t.first), BddLevel(p, t.second));
    int v;
    if(BddLevel(p, t.first) == l) v = BddVar(p, t.first);
    if(BddLevel(p, t.second) == l) v = BddVar(p, t.second);
    std::pair<int, int> t0, t1;
    t0 = cs[t].first;
    t1 = cs[t].second;
    // check new children
    bool c0 = 0, c1 = 0;
    while(m.count(t0)) {
      if(t0 == m[t0].first) {
	assert(!m[t0].second);
	break;
      }
      c0 ^= m[t0].second;
      t0 = m[t0].first;
    }
    t0.first = LitNotCond(t0.first, c0);
    while(m.count(t1)) {
      if(t1 == m[t1].first) {
	assert(!m[t1].second);
	break;
      }
      c1 ^= m[t1].second;
      t1 = m[t1].first;
    }
    t1.first = LitNotCond(t1.first, c1);
    // trivial cases
    if(t0 == cs[t].first && t1 == cs[t].second) {
      m[t] = std::make_pair(t, 0);
      continue;
    }
    if(t0.second == 1) {
      BddIncRef(p, t1.first), BddIncRef(p, t1.second);
      m[t] = std::make_pair(t1, 0);
      continue;
    }
    if(t1.second == 1) {
      BddIncRef(p, t0.first), BddIncRef(p, t0.second);
      m[t] = std::make_pair(t0, 0);
      continue;
    }
    // create new node
    int tf, tg;
    if(t0.first == t1.first) tf = t0.first;
    else tf = BddUniqueCreate(p, v, t1.first, t0.first);
    BddIncRef(p, tf);
    if(t0.second == t1.second) tg = t0.second;
    else tg = BddUniqueCreate(p, v, t1.second, t0.second);
    BddIncRef(p, tg);
    m[t] = std::make_pair(std::make_pair(tf, tg), 0);
    assert(t != m[t].first);
  }
  for(auto t : res) {
    BddDecRef(p, t.first), BddDecRef(p, t.second);
    if(m[t].first == t) continue;
    BddDecRef(p, m[t].first.first), BddDecRef(p, m[t].first.second);
  }
  if(m.count(root)) return LitNotCond(m[root].first.first, m[root].second);
  return root.first;
}

/**Function*************************************************************
   Synopsis    [main]
   Description []
               
   SideEffects []
   SeeAlso     []
***********************************************************************/
void bddlearn(std::vector<boost::dynamic_bitset<> > const & inputs, boost::dynamic_bitset<> const & output, std::string aigname, bool reo) {
  int ninputs = inputs.size();
  BddMan * p = BddManAlloc(ninputs + 1, 25);

  // reorder for some set
  if(reo) {
    // read patterns
    int onset = 0;
    BddIncRef(p, onset);
    int offset = 0;
    BddIncRef(p, offset);
    int tmp;
    for(int i = 0; i < inputs[0].size(); i++) {
      int minterm = 1;
      BddIncRef(p, minterm);
      for(int j = 0; j < inputs.size(); j++) {
	if(inputs[j][i])
	  tmp = BddAnd(p, minterm, BddIthVar(j));
	else
	  tmp = BddAnd(p, minterm, LitNot(BddIthVar(j)));
	BddIncRef(p, tmp);
	BddDecRef(p, minterm);
	minterm = tmp;
      }
      if(output[i]) {
	tmp = BddOr(p, onset, minterm);
	BddIncRef(p, tmp);
	BddDecRef(p, onset), BddDecRef(p, minterm);
	onset = tmp;
      }
      else {
	tmp = BddOr(p, offset, minterm);
	BddIncRef(p, tmp);
	BddDecRef(p, offset), BddDecRef(p, minterm);
	offset = tmp;
      }
    }

    int x;
    //x = BddOr(p, BddAnd(p, onset, BddIthVar(ninputs)), BddAnd(p, offset, LitNot(BddIthVar(ninputs))));
    x = onset;
    //x = offset;
    
    BddIncRef(p, x);
    BddDecRef(p, onset);
    BddDecRef(p, offset);
    
    std::cout << "before reo : " << BddCountNodes(p, x) << std::endl;
    BddSiftReorder(p);
    std::cout << "after reo : " << BddCountNodes(p, x) << std::endl;
    std::cout << "ordering : " << std::endl;
    for(int i = 0; i < p->nVars; i++)
      std::cout << "pi" << BddLevel2Var(p, i) << ", ";
    std::cout << std::endl;
    BddDecRef(p, x);
  }

  // transfer ordering
  BddMan * p2 = BddManAlloc(ninputs + 1, 25);
  for(int i = 0; i < ninputs; i++)
    p2->pLevels[i] = p->pLevels[i];
  BddPrintRef(p);
  assert(p->pRefs[0] == 0);
  BddManFree(p);
  p = p2;

  // read patterns
  int onset = 0;
  BddIncRef(p, onset);
  int offset = 0;
  BddIncRef(p, offset);
  int tmp;
  for(int i = 0; i < inputs[0].size(); i++) {
    int minterm = 1;
    BddIncRef(p, minterm);
    for(int j = 0; j < inputs.size(); j++) {
      if(inputs[j][i])
	tmp = BddAnd(p, minterm, BddIthVar(j));
      else
	tmp = BddAnd(p, minterm, LitNot(BddIthVar(j)));
      BddIncRef(p, tmp);
      BddDecRef(p, minterm);
      minterm = tmp;
    }
    if(output[i]) {
      tmp = BddOr(p, onset, minterm);
      BddIncRef(p, tmp);
      BddDecRef(p, onset), BddDecRef(p, minterm);
      onset = tmp;
    }
    else {
      tmp = BddOr(p, offset, minterm);
      BddIncRef(p, tmp);
      BddDecRef(p, offset), BddDecRef(p, minterm);
      offset = tmp;
    }
  }

  std::cout << "onset : " << BddCountNodes(p, onset) << std::endl;
  std::cout << "offset : " << BddCountNodes(p, offset) << std::endl;

  int x;
  int careset;

  careset = BddOr(p, onset, offset);
  BddIncRef(p, careset);

  x = BddSqueeze(p, onset, LitNot(offset), 0);
  std::cout << "squeeze : " << BddCountNodes(p, x) << std::endl;
  BddIncRef(p, x), assert(BddOr(p, BddAnd(p, onset, LitNot(x)), BddAnd(p, offset, x)) == 0), BddDecRef(p, x);
  
  x = BddSqueeze(p, onset, LitNot(offset), 1);
  std::cout << "squeeze inter : " << BddCountNodes(p, x) << std::endl;
  BddIncRef(p, x), assert(BddOr(p, BddAnd(p, onset, LitNot(x)), BddAnd(p, offset, x)) == 0), BddDecRef(p, x);
  
  x = BddRestrict(p, onset, careset);
  std::cout << "restrict : " << BddCountNodes(p, x) << std::endl;
  BddIncRef(p, x), assert(BddOr(p, BddAnd(p, onset, LitNot(x)), BddAnd(p, offset, x)) == 0), BddDecRef(p, x);

  x = BddMinimize3(p, onset, LitNot(careset), 0);
  std::cout << "minimize : " << BddCountNodes(p, x) << std::endl;
  BddIncRef(p, x), assert(BddOr(p, BddAnd(p, onset, LitNot(x)), BddAnd(p, offset, x)) == 0), BddDecRef(p, x);
  
  x = BddMinimize3(p, onset, LitNot(careset), 1);
  std::cout << "minimize inter : " << BddCountNodes(p, x) << std::endl;
  BddIncRef(p, x), assert(BddOr(p, BddAnd(p, onset, LitNot(x)), BddAnd(p, offset, x)) == 0), BddDecRef(p, x);
  
  x = BddMinimizeLevelTD(p, onset, LitNot(careset));
  std::cout << "bminimize : " << BddCountNodes(p, x) << std::endl;
  BddIncRef(p, x), assert(BddOr(p, BddAnd(p, onset, LitNot(x)), BddAnd(p, offset, x)) == 0), BddDecRef(p, x);
  
  x = BddMinimize3(p, onset, LitNot(careset), 0);
  x = BddMinimizeLevelTD(p, x, LitNot(careset));
  std::cout << "bmin with pre : " << BddCountNodes(p, x) << std::endl;
  BddIncRef(p, x), assert(BddOr(p, BddAnd(p, onset, LitNot(x)), BddAnd(p, offset, x)) == 0), BddDecRef(p, x);

  // write output;
  aigman * aig = GenAig(p, x, ninputs);
  aig->write(aigname);
  delete aig;

  // verify and quit
  BddDecRef(p, onset);
  BddDecRef(p, offset);
  BddDecRef(p, careset);
  BddPrintRef(p);
  assert(p->pRefs[0] == 0);
  BddManFree(p);
}

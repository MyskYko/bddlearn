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
struct BddMan_ 
{
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
    unsigned           nUniqueMask;   // selection mask for unique table
    unsigned           nCacheMask;    // selection mask for computed table
    int                nCacheLookups; // the number of computed table lookups
    int                nCacheMisses;  // the number of computed table misses

  int * pEdges;
  std::vector<std::list<int> > nodelist;
};

int Var2Lit( int i, bool c ) { return i << 1 + (int)c; }
int Lit2Var( int i ) { return i >> 1; }
int LitIsCompl( int i ) { return i & 1; }
int LitRegular( int i ) { return i & ~1; }
int LitNot( int i ) { return i ^ 1; }
int LitNotCond( int i, bool c ) { return i ^ (int)c; }

int BddIthVar( int i ) { return Var2Lit(i + 1, 0); }
unsigned BddHash( int Arg0, int Arg1, int Arg2 ) { return 12582917 * Arg0 + 4256249 * Arg1 + 741457 * Arg2; }

int Var2Level( BddMan * p, int i ) { return p->pLevels[i]; }
int Level2Var( BddMan * p, int i ) {
  for(int v = 0; v < p->nVars; v++)
    if(i == p->pLevels[v])
      return v;
  abort();
}

int BddVar( BddMan * p, int i ) { return p->pVars[Lit2Var(i)]; }
int BddLevel( BddMan * p, int i ) { return Var2Level(p, BddVar(p, i)); }
int BddThen( BddMan * p, int i ) { return LitNotCond(p->pObjs[LitRegular(i)], LitIsCompl(i)); }
int BddElse( BddMan * p, int i ) { return LitNotCond(p->pObjs[LitRegular(i)+1], LitIsCompl(i)); }

int BddMark( BddMan * p, int i ) { return p->pMark[Lit2Var(i)]; }
void BddSetMark( BddMan * p, int i, int m ){ p->pMark[Lit2Var(i)] = m; }

int BddEdge( BddMan * p, int i ) { return p->pEdges[Lit2Var(i)]; }
void BddIncEdge( BddMan *p, int i ) { if(i == 0 || i == 1) return; p->pEdges[Lit2Var(i)]++; assert(p->pEdges[Lit2Var(i)] > 0); }
void BddDecEdge( BddMan *p, int i ) { if(i == 0 || i == 1) return; p->pEdges[Lit2Var(i)]--; assert(p->pEdges[Lit2Var(i)] >= 0); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************
  Synopsis    [Creating new node.]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddUniqueCreateInt( BddMan * p, int Var, int Then, int Else )
{
    int *q = p->pUnique + (BddHash(Var, Then, Else) & p->nUniqueMask);
    for ( ; *q; q = p->pNexts + *q )
        if ( (int)p->pVars[*q] == Var && p->pObjs[*q+*q] == Then && p->pObjs[*q+*q+1] == Else )
            return Var2Lit(*q, 0);
    if ( p->nObjs == p->nObjsAlloc )
        printf( "Aborting because the number of nodes exceeded %d.\n", p->nObjsAlloc ), fflush(stdout);
    assert( p->nObjs < p->nObjsAlloc );     
    *q = p->nObjs++;
    p->pVars[*q] = Var;
    p->pObjs[*q+*q] = Then;
    p->pObjs[*q+*q+1] = Else;
//    printf( "Added node %3d: Var = %3d.  Then = %3d.  Else = %3d\n", *q, Var, Then, Else );
    assert( !LitIsCompl(Else) );
    return Var2Lit(*q, 0);
}
int BddUniqueCreate( BddMan * p, int Var, int Then, int Else )
{
    assert( Var >= 0 && Var < p->nVars );
    assert( Var2Level(p, Var) < BddLevel(p, Then) );
    assert( Var2Level(p, Var) < BddLevel(p, Else) );
    if ( Then == Else )
        return Else;
    if ( !LitIsCompl(Else) )
        return BddUniqueCreateInt( p, Var, Then, Else );
    return LitNot( BddUniqueCreateInt(p, Var, LitNot(Then), LitNot(Else)) );
}

/**Function*************************************************************
  Synopsis    []
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddCacheLookup( BddMan * p, int Arg1, int Arg2 )
{
    int * pEnt = p->pCache + 3*(BddHash(0, Arg1, Arg2) & p->nCacheMask);
    p->nCacheLookups++;
    return (pEnt[0] == Arg1 && pEnt[1] == Arg2) ? pEnt[2] : -1;
}
int BddCacheInsert( BddMan * p, int Arg1, int Arg2, int Res )
{
    int * pEnt = p->pCache + 3*(BddHash(0, Arg1, Arg2) & p->nCacheMask);
    pEnt[0] = Arg1;  pEnt[1] = Arg2;  pEnt[2] = Res;
    p->nCacheMisses++;
    assert( Res >= 0 );
    return Res;
}
void BddCacheClear( BddMan * p )
{
    free(p->pCache);
    p->pCache = (int*)calloc( 3*(p->nCacheMask + 1), sizeof(int) );
}


/**Function*************************************************************
  Synopsis    []
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
BddMan * BddManAlloc( int nVars, int nPowTwo )
{
    BddMan * p; int i;
    p = (BddMan*)calloc( 1, sizeof(BddMan) );
    p->nVars       = nVars;
    p->nObjsAlloc  = 1 << nPowTwo;
    p->nUniqueMask = (1 << nPowTwo) - 1;
    p->nCacheMask  = (1 << nPowTwo) - 1;
    p->pUnique     = (int*)calloc( p->nUniqueMask + 1, sizeof(int) );
    p->pNexts      = (int*)calloc( p->nObjsAlloc, sizeof(int) );
    p->pCache      = (int*)calloc( 3*(p->nCacheMask + 1), sizeof(int) );
    p->pObjs       = (int*)calloc( 2*p->nObjsAlloc, sizeof(int) );
    p->pMark       = (unsigned char *)calloc( p->nObjsAlloc, sizeof(char) );
    p->pVars       = (unsigned short*)calloc( p->nObjsAlloc, sizeof(short) );
    p->pLevels     = (unsigned short*)calloc( p->nVars + 1, sizeof(short) );
    for ( i = 0; i < nVars + 1; i++ )
        p->pLevels[i] = i;
    p->pVars[0]    = p->nVars;
    p->nObjs       = 1;
    for ( i = 0; i < nVars; i++ )
        BddUniqueCreate( p, i, 1, 0 );
    assert( p->nObjs == nVars + 1 );
    p->pEdges = NULL;
    return p;
}
void BddManFree( BddMan * p )
{
    printf( "BDD stats: Var = %d  Obj = %d  Alloc = %d  Hit = %d  Miss = %d\n", 
        p->nVars, p->nObjs, p->nObjsAlloc, p->nCacheLookups-p->nCacheMisses, p->nCacheMisses );
    free( p->pUnique );
    free( p->pNexts );
    free( p->pCache );
    free( p->pObjs );
    free( p->pVars );
    free( p->pLevels );
    if(p->pEdges) free(p->pEdges);
    free( p );
}

/**Function*************************************************************
  Synopsis    [Boolean AND.]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddAnd( BddMan * p, int a, int b )
{
    int v, r0, r1, r;
    if ( a == 0 ) return 0;
    if ( b == 0 ) return 0;
    if ( a == 1 ) return b;
    if ( b == 1 ) return a;
    if ( a == b ) return a;
    if ( a > b )  return BddAnd( p, b, a );
    if ( (r = BddCacheLookup(p, a, b)) >= 0 )
        return r;
    if ( BddLevel(p, a) < BddLevel(p, b) )
        v  = BddVar(p, a),
        r0 = BddAnd( p, BddElse(p, a), b ),
        r1 = BddAnd( p, BddThen(p, a), b );
    else if ( BddLevel(p, a) > BddLevel(p, b) )
        v  = BddVar(p, b),
        r0 = BddAnd( p, a, BddElse(p, b) ), 
        r1 = BddAnd( p, a, BddThen(p, b) );
    else // if ( BddVar(p, a) == BddVar(p, b) )
        v  = BddVar(p, a),
        r0 = BddAnd( p, BddElse(p, a), BddElse(p, b) ), 
        r1 = BddAnd( p, BddThen(p, a), BddThen(p, b) );
    r = BddUniqueCreate( p, v, r1, r0 );
    return BddCacheInsert( p, a, b, r );
}
int BddOr( BddMan * p, int a, int b )
{
    return LitNot( BddAnd(p, LitNot(a), LitNot(b)) );
}
int BddXor( BddMan * p, int a, int b )
{
    int r0, r1;
    r0 = BddAnd( p, LitNot(a), b );
    r1 = BddAnd( p, a, LitNot(b) );
    return BddOr( p, r0, r1 );
}
/**Function*************************************************************
  Synopsis    [Swap levels at i and i + 1.]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
void BddRecursiveRef( BddMan * p, int x )
{
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
void BddDeregister( BddMan * p, int a )
{
  int Var, Then, Else;
  Var = p->pVars[a], Then = p->pObjs[a+a], Else = p->pObjs[a+a+1];
  int *q = p->pUnique + (BddHash(Var, Then, Else) & p->nUniqueMask);
  for ( ; *q; q = p->pNexts + *q )
    if(*q == a) {
      *q = p->pNexts[*q];
      return;
    }
  abort();
}
void BddSwap( BddMan * p, int i )
{
  assert(!p->nodelist.empty());
  assert(p->pEdges);
  int uv = Level2Var(p, i);
  int lv = Level2Var(p, i + 1);
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
    BddDecEdge(p, t);
    if(BddVar(p, t) == lv) {
      tt = BddThen(p, t), te = BddElse(p, t);
      if(BddEdge(p, t) == 0) BddDecEdge(p, tt), BddDecEdge(p, te);
    }
    else tt = te = t;
    BddDecEdge(p, e);
    if(BddVar(p, e) == lv) {
      et = BddThen(p, e), ee = BddElse(p, e);
      if(BddEdge(p, e) == 0) BddDecEdge(p, et), BddDecEdge(p, ee);
    }
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
    // reregister the new node with new children, and push it into list
    BddDeregister(p, a);
    int Var, Then, Else;
    Var = lv, Then = nt, Else = ne;
    assert( Then != Else );
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
}


/**Function*************************************************************
  Synopsis    [Counting nodes.]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddCount_rec( BddMan * p, int i )
{
    if ( i < 2 )
        return 0;
    if ( BddMark(p, i) )
        return 0;
    BddSetMark( p, i, 1 );
    return 1 + BddCount_rec(p, BddElse(p, i)) + BddCount_rec(p, BddThen(p, i));
}
void BddUnmark_rec( BddMan * p, int i )
{
    if ( i < 2 )
        return;
    if ( !BddMark(p, i) )
        return;
    BddSetMark( p, i, 0 );
    BddUnmark_rec( p, BddElse(p, i) );
    BddUnmark_rec( p, BddThen(p, i) );
}
int BddCountNodes( BddMan * p, int i )
{
    int Count = BddCount_rec( p, i );
    BddUnmark_rec( p, i );
    return Count;
}
int BddCountNodes( BddMan * p, int i, int j )
{
    int Count = BddCount_rec( p, i );
    Count += BddCount_rec( p, j );
    BddUnmark_rec( p, i );
    BddUnmark_rec( p, j );
    return Count;
}

/*
int BddCountNodesArray( BddMan * p, Vec_Int_t * vNodes )
{
    int i, a, Count = 0;
    Vec_IntForEachEntry( vNodes, a, i )
        Count += BddCount_rec( p, a );
    Vec_IntForEachEntry( vNodes, a, i )
        BddUnmark_rec( p, a );
    return Count;
}
int BddCountNodesArray2( BddMan * p, Vec_Int_t * vNodes )
{
    int i, a, Count = 0;
    Vec_IntForEachEntry( vNodes, a, i )
    {
        Count += BddCount_rec( p, a );
        BddUnmark_rec( p, a );
    }
    return Count;
}
*/

/**Function*************************************************************
  Synopsis    [Count ones]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddCountOnes_rec(BddMan * p, int x, std::string & s) {
  if(x == 1)
    {
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
  for(int i = 0; i < p->nVars; i++) {
    s += "-";
  }
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
  Synopsis    [Printing BDD.]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
void BddPrint_rec( BddMan * p, int a, int * pPath )
{
    if ( a == 0 ) 
        return;
    if ( a == 1 )
    { 
        int i;
        for ( i = 0; i < p->nVars; i++ )
            if ( pPath[i] == 0 || pPath[i] == 1 )
                printf( "%c%d", pPath[i] ? '+' : '-', i );
        printf( " " );
        return; 
    }
    pPath[BddVar(p, a)] =  0;
    BddPrint_rec( p, BddElse(p, a), pPath );
    pPath[BddVar(p, a)] =  1;
    BddPrint_rec( p, BddThen(p, a), pPath );
    pPath[BddVar(p, a)] = -1;
}
void BddPrint( BddMan * p, int a )
{
    int * pPath = (int*)calloc( p->nVars, sizeof(int) );
    printf( "BDD %d = ", a );
    BddPrint_rec( p, a, pPath );
    free( pPath );
    printf( "\n" );
}
void BddPrintTest( BddMan * p )
{
    int bVarA = BddIthVar(0);
    int bVarB = BddIthVar(1);
    int bVarC = BddIthVar(2);
    int bVarD = BddIthVar(3);
    int bAndAB = BddAnd( p, bVarA, bVarB );
    int bAndCD = BddAnd( p, bVarC, bVarD );
    int bFunc  = BddOr( p, bAndAB, bAndCD );
    BddPrint( p, bFunc );
    printf( "Nodes = %d\n", BddCountNodes(p, bFunc) );
}

/**Function*************************************************************
  Synopsis    [bdd2aig]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int GenAig_rec(BddMan * man, aigman * aig, std::map<int, int> & m, int x) {
  if ( x == 0 ) {
    return 0;
  }
  if ( x == 1 ) {
    return 1;
  }
  if ( LitIsCompl(x) ) {
    return GenAig_rec( man, aig, m, LitNot(x) ) ^ 1;
  }
  if ( m.count( x ) ) {
    return m[x];
  }
  int c = (BddVar( man, x ) + 1) << 1;
  int f1 = GenAig_rec( man, aig, m, BddThen( man, x ) );
  int f0 = GenAig_rec( man, aig, m, BddElse( man, x ) );
  int f = aig->newite( c, f1, f0 );
  m[x] = f;
  return f;
}

aigman *GenAig(BddMan * man, int x) {
  aigman *p = new aigman( man->nVars );
  std::map<int, int> m;
  int f = GenAig_rec( man, p, m, x );
  p->newpo(f);
  return p;
}

/**Function*************************************************************
  Synopsis    [traditional reduction using care-set]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddRestrict( BddMan * p, int f, int c )
{
    assert( c );
    int r0, r1;
    if ( c == 1 ) return f;
    if ( f == 0 || f == 1 ) return f;
    if ( !BddElse(p, c) ) return BddRestrict( p, f, BddThen(p, c) );
    if ( !BddThen(p, c) ) return BddRestrict( p, f, BddElse(p, c) );
    if ( BddLevel(p, f) > BddLevel(p, c) )
      return BddRestrict( p, f, BddOr( p, BddElse(p, c), BddThen(p, c) ) );
    if ( BddLevel(p, f) < BddLevel(p, c) )
        r0 = BddRestrict( p, BddElse(p, f), c ),
        r1 = BddRestrict( p, BddThen(p, f), c );
    else
        r0 = BddRestrict( p, BddElse(p, f), BddElse(p, c) ),
        r1 = BddRestrict( p, BddThen(p, f), BddThen(p, c) );
    return BddUniqueCreate( p, BddVar(p, f), r1, r0 );
}

/**Function*************************************************************
  Synopsis    [traditional squeeze between l (lower) and u (upper) bound]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddSqueeze( BddMan * p, int l, int u, bool finter = 1, bool fhigheffort = 0 )
{
  if (l == 0) return l;
  if (u == 1) return u;
  int topu, topl, index, le, lt, ue, ut;
  topu = BddLevel( p, u );
  topl = BddLevel( p, l );
  if ( topu <= topl ) {
    index = BddVar( p, u );
    ut = BddThen( p, u ); ue = BddElse( p, u );
  } else {
    index = BddVar( p, l );
    ut = ue = u;
  }
  if ( topl <= topu ) {
    lt = BddThen( p, l ); le = BddElse( p, l );
  } else {
    lt = le = l;
  }
  int r;
  if ( BddOr( p, LitNot(lt), le ) == 1 && BddOr( p, LitNot(ue), ut ) == 1 )
    return BddSqueeze( p, le, ue, finter, fhigheffort );
  if ( BddOr( p, LitNot(le), lt ) == 1 && BddOr( p, LitNot(ut), ue ) == 1 )
    return BddSqueeze( p, lt, ut, finter, fhigheffort );
  if(finter) {
    if ( BddOr( p, LitNot(le), LitNot(ut) ) == 1 && BddOr( p, ue, lt ) == 1 ) {
      r = BddSqueeze( p, lt, ut, finter, fhigheffort );
      return BddUniqueCreate( p, index, r, LitNot(r) );
    }
    if ( BddOr( p, LitNot(lt), LitNot(ue) ) == 1 && BddOr( p, ut, le ) == 1 ) {
      r = BddSqueeze( p, le, ue, finter, fhigheffort );
      return BddUniqueCreate( p, index, LitNot(r), r );
    }
  }
  int ar = -1;
  if(fhigheffort) {
    if ( BddOr( p, LitNot(lt), ue ) == 1 && BddOr( p, LitNot(le), ut ) == 1 ) {
      int au, al;
      au = BddAnd( p, ut, ue );
      al = BddOr( p , lt, le );
      ar = BddSqueeze( p, al, au, finter, fhigheffort );
    }
  }
  int t, e;
  t = BddSqueeze( p, lt, ut, finter, fhigheffort );
  e = BddSqueeze( p, le, ue, finter, fhigheffort );
  r = (t == e) ? t : BddUniqueCreate( p, index, t, e );
  if ( ar != -1 )
    if ( BddCountNodes( p, ar ) <= BddCountNodes( p, r ) )
      r = ar;
  return r;
}

/**Function*************************************************************
  Synopsis    [minimize with DC]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
bool BddCheckIntersect( BddMan * p, int af, int ag, int bf, int bg ) {
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
int BddDCIntersect2( BddMan * p, int af, int ag, int bf, int bg )
{
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
  int r0, r1;
  r0 = BddDCIntersect2(p, af0, ag0, bf0, bg0);
  r1 = BddDCIntersect2(p, af1, ag1, bf1, bg1);
  return BddUniqueCreate( p, v, r1, r0 );
}
int BddMinimize3( BddMan * p, int f, int g, bool finter = 1 )
{
  // terminal (care set)
  if(g == 0) return f;
  assert(g != 1);
  // top var
  if(BddLevel(p, f) > BddLevel(p, g))
    return BddMinimize3(p, f, BddAnd(p, BddElse(p, g), BddThen(p, g)), finter);
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
	int f2 = BddDCIntersect2( p, f0, g0, f1, g1 );
	int g2 = BddAnd( p, g0, g1 );
	return BddMinimize3( p, f2, g2, finter );
      }
      if(BddCheckIntersect(p, LitNot(f0), g0, f1, g1)) {
	int f2 = BddDCIntersect2( p, LitNot(f0), g0, f1, g1 );
	int g2 = BddAnd( p, g0, g1 );
	int r = BddMinimize3( p, f2, g2, finter );
	return BddUniqueCreate( p, var, r, LitNot(r) );      
      }
    }
  }
  // recurse for each case
  int r0, r1;
  r0 = BddMinimize3(p, f0, g0, finter);
  r1 = BddMinimize3(p, f1, g1, finter);
  return BddUniqueCreate( p, var, r1, r0 );
}
/**Function*************************************************************
  Synopsis    [minimize with DC]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
void BddBreadthMinimize_level( BddMan * p, std::vector<std::pair<int, int> > & ts, std::map<std::pair<int, int>, std::pair<std::pair<int, int>, bool> > & m, double maxinc = 1.1 ) {
  std::vector<std::pair<int, int> > tsold = ts;
  std::vector<int> c(ts.size());
  for(int i = 0; i < ts.size(); i++) {
    c[i] = i + 1;
  }
  // compare one (const)
  for(int i = 0; i < ts.size(); i++) {
    if(BddOr(p, ts[i].first, ts[i].second) == 1) {
      ts[i].first = 1;
      c[i] = 0;
      continue;
    }
    if(BddOr(p, LitNot(ts[i].first), ts[i].second) == 1) {
      ts[i].first = 0;
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
	int f2 = BddDCIntersect2( p, ts[i].first, ts[i].second, ts[j].first, ts[j].second );
	int next = BddCountNodes(p, f2);
	if(next < prev * maxinc) {
	  int g2 = BddAnd( p, ts[i].second, ts[j].second );
	  ts[i].first = f2;
	  ts[i].second = g2;
	  c[j] = i + 1;
	  continue;
	}
      }
      if(BddCheckIntersect(p, ts[i].first, ts[i].second, LitNot(ts[j].first), ts[j].second)) {
	int f2 = BddDCIntersect2( p, ts[i].first, ts[i].second, LitNot(ts[j].first), ts[j].second );
	int next = BddCountNodes(p, f2);
	if(next < prev * maxinc) {
	  int g2 = BddAnd( p, ts[i].second, ts[j].second );
	  ts[i].first = f2;
	  ts[i].second = g2;
	  c[j] = -(i + 1);
	  continue;
	}
      }
    }
  }
  // map registeration, replace by new nodes
  std::vector<std::pair<int, int> > tsnew;
  for(int i = 0; i < ts.size(); i++) {
    if(c[i] == i + 1) {
      if(tsold[i] != ts[i]) {
	m[tsold[i]] = std::make_pair(ts[i], 0);
      }
      tsnew.push_back(ts[i]);
    }
    else if(c[i] == 0) {
      m[tsold[i]] = std::make_pair(ts[i], 0);
    }
    else {
      m[tsold[i]] = std::make_pair(ts[abs(c[i]) - 1], c[i] < 0);
    }
  }
  ts = tsnew;
}
int BddBreadthMinimize( BddMan * p, int f, int g ) {
  std::set<std::pair<int, int> > fronts;
  std::map<std::pair<int, int>, std::pair<std::pair<int, int>, bool> > m;
  std::map<std::pair<int, int>, std::pair<std::pair<int, int>, std::pair<int, int> > > cs;
  std::vector<std::pair<int, int> > res;
  std::pair<int, int> root(f, g);
  fronts.insert(root);
  for(int i = 0; i < p->nVars; i++) {
    // get nodes in the level
    std::vector<std::pair<int, int> > targets;
    std::set<std::pair<int, int> > nfronts;
    for(auto it = fronts.begin(); it != fronts.end();) {
      if(BddLevel(p, it->first) == i) {
	targets.push_back(*it);
	it = fronts.erase(it);
      }
      else if(BddLevel(p, it->second) == i) {
	nfronts.insert(std::make_pair(it->first, BddAnd(p, BddElse(p, it->second), BddThen(p, it->second))));
	it = fronts.erase(it);
      }
      else {
	++it;
      }
    }
    fronts.insert(nfronts.begin(), nfronts.end());
    // minimize the level
    if(targets.size() > 1) {
      BddBreadthMinimize_level(p, targets, m);
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
      if(t0g != 1) fronts.insert(t0);
      if(t1g != 1) fronts.insert(t1);
      res.push_back(t);
    }
  }
  // construct
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
    if(t0.second == 1) {
      m[t] = std::make_pair(t1, 0);
      continue;
    }
    if(t1.second == 1) {
      m[t] = std::make_pair(t0, 0);
      continue;
    }
    // check new children
    if(!m.count(t0) && !m.count(t1)) continue;
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
    // create new node
    int tf, tg;
    if(t0.first == t1.first) tf = t0.first;
    else tf = BddUniqueCreate(p, v, t1.first, t0.first);
    if(t0.second == t1.second) tg = t0.second;
    else tg = BddUniqueCreate(p, v, t1.second, t0.second);
    m[t] = std::make_pair(std::make_pair(tf, tg), 0);
  }
  if(m.count(root)) return LitNotCond(m[root].first.first, m[root].second);
  return root.first;
}
int BddBreadthMinimize2( BddMan * p, int f, int g ) {
  std::vector<std::pair<int, int> > targets;
  std::vector<std::vector<std::pair<int, int> > > nodes(p->nVars);
  std::map<std::pair<int, int>, std::pair<std::pair<int, int>, bool> > m;
  std::map<std::pair<int, int>, std::pair<std::pair<int, int>, std::pair<int, int> > > cs;
  std::pair<int, int> root(f, g);
  targets.push_back(root);
  // get nodes in each level
  for(int i = 0; i < targets.size(); i++) {
    auto t = targets[i];
    if(t.second == 1) continue;
    if(t.first == 0 || t.first == 1) continue;
    //std::cout << t.first << "," << t.second << std::endl;
    int l = std::min(BddLevel(p, t.first), BddLevel(p, t.second));
    nodes[l].push_back(t);
    int v, t0f, t0g, t1f, t1g;
    if(BddLevel(p, t.first) == l) v = BddVar(p, t.first), t0f = BddElse(p, t.first), t1f = BddThen(p, t.first);
    else t0f = t1f = t.first;
    if(BddLevel(p, t.second) == l) v = BddVar(p, t.second), t0g = BddElse(p, t.second), t1g = BddThen(p, t.second);
    else t0g = t1g = t.second;
    //std::cout << t0f << "," << t0g << " " << t1f << "," << t1g << std::endl;
    std::pair<int, int> t0, t1;
    t0 = std::make_pair(t0f, t0g);
    t1 = std::make_pair(t1f, t1g);
    cs[t] = std::make_pair(t0, t1);
    targets.push_back(t0);
    targets.push_back(t1);
  }
  // minimize each level
  for(int l = p->nVars - 1; l >= 0; l--) {
    int v = Level2Var(p, l);
    // build current nodes
    std::set<std::pair<int, int> > s;
    for(auto t : nodes[l]) {
      std::pair<int, int> t0, t1;
      t0 = cs[t].first;
      t1 = cs[t].second;
      // no change
      if(!m.count(t0) && !m.count(t1)) {
	s.insert(t);
	continue;
      }
      // get new children
      int c0 = 0, c1 = 0;
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
      // create new node
      int tf, tg;
      if(t0.first == t1.first) tf = t0.first;
      else tf = BddUniqueCreate(p, v, t1.first, t0.first);
      if(t0.second == t1.second) tg = t0.second;
      else tg = BddUniqueCreate(p, v, t1.second, t0.second);
      m[t] = std::make_pair(std::make_pair(tf, tg), 0);
      s.insert(m[t].first);
    }
    std::cout << "lev " << l << " num " << s.size() << std::endl;
    // minimize the level
    targets.clear();
    for(auto t : s) {
      targets.push_back(t);
    }
    if(targets.size() > 1) {
      BddBreadthMinimize_level(p, targets, m);
    }
  }
  // get new root
  int c = 0;
  while(m.count(root)) {
    if(root == m[root].first) {
      assert(!m[root].second);
      break;
    }
    c ^= m[root].second;
    root = m[root].first;
  }
  return LitNotCond(root.first, c);
}

/**Function*************************************************************
  Synopsis    [main]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
void bddlearn(std::vector<boost::dynamic_bitset<> > const & inputs, boost::dynamic_bitset<> const & output, std::string aigname, std::vector<boost::dynamic_bitset<> > const * einputs = NULL, boost::dynamic_bitset<> const * eoutput = NULL) {
  int ninputs = inputs.size();
  BddMan * p = BddManAlloc(ninputs, 25);
  int onset = 0;
  int offset = 0;
  for(int i = 0; i < inputs[0].size(); i++) {
    int minterm = 1;
    for(int j = 0; j < inputs.size(); j++) {
      if(inputs[j][i]) {
	minterm = BddAnd(p, minterm, BddIthVar(j));
      }
      else {
	minterm = BddAnd(p, minterm, LitNot(BddIthVar(j)));
      }
    }
    if(output[i]) {
      onset = BddOr(p, onset, minterm);
    }
    else {
      offset = BddOr(p, offset, minterm);
    }
  }
  
  int eonset = 0;
  int eoffset = 0;
  int etotal = 0;
  if(eoutput) {
    etotal = (*einputs)[0].size();
    for(int i = 0; i < (*einputs)[0].size(); i++) {
      int minterm = 1;
      for(int j = 0; j < (*einputs).size(); j++) {
	if((*einputs)[j][i]) {
	  minterm = BddAnd(p, minterm, BddIthVar(j));
	}
	else {
	  minterm = BddAnd(p, minterm, LitNot(BddIthVar(j)));
	}
      }
      if((*eoutput)[i]) {
	eonset = BddOr(p, eonset, minterm);
      }
      else {
	eoffset = BddOr(p, eoffset, minterm);
      }
    }
  }

  std::cout << "onset : " << BddCountNodes(p, onset) << std::endl;
  std::cout << "offset : " << BddCountNodes(p, offset) << std::endl;

  aigman * aig;
  int x;
  int careset = BddOr(p, onset, offset);
  
  x = BddSqueeze(p, onset, LitNot(offset), 0);
  std::cout << "squeeze : " << BddCountNodes(p, x);
  if(etotal) {
    int error = BddOr(p, BddAnd(p, eonset, LitNot(x)), BddAnd(p, eoffset, x));
    std::cout << " (" << 100 * (1 - ((double)BddCountOnes(p, error) / etotal)) << "%)";
  }
  std::cout << std::endl;

  x = BddSqueeze(p, onset, LitNot(offset), 1);
  std::cout << "squeeze inter : " << BddCountNodes(p, x);
  if(etotal) {
    int error = BddOr(p, BddAnd(p, eonset, LitNot(x)), BddAnd(p, eoffset, x));
    std::cout << " (" << 100 * (1 - ((double)BddCountOnes(p, error) / etotal)) << "%)";
  }
  std::cout << std::endl;
  /*
  x = BddRestrict(p, onset, careset);
  std::cout << "restrict : " << BddCountNodes(p, x);
  if(etotal) {
    int error = BddOr(p, BddAnd(p, eonset, LitNot(x)), BddAnd(p, eoffset, x));
    std::cout << " (" << 100 * (1 - ((double)BddCountOnes(p, error) / etotal)) << "%)";
  }
  std::cout << std::endl;
  */
  x = BddMinimize3(p, onset, LitNot(careset), 0);
  std::cout << "minimize : " << BddCountNodes(p, x);
  if(etotal) {
    int error = BddOr(p, BddAnd(p, eonset, LitNot(x)), BddAnd(p, eoffset, x));
    std::cout << " (" << 100 * (1 - ((double)BddCountOnes(p, error) / etotal)) << "%)";
  }
  std::cout << std::endl;

  x = BddMinimize3(p, onset, LitNot(careset), 1);
  std::cout << "minimize inter : " << BddCountNodes(p, x);
  if(etotal) {
    int error = BddOr(p, BddAnd(p, eonset, LitNot(x)), BddAnd(p, eoffset, x));
    std::cout << " (" << 100 * (1 - ((double)BddCountOnes(p, error) / etotal)) << "%)";
  }
  std::cout << std::endl;

  x = BddBreadthMinimize(p, onset, LitNot(careset));
  std::cout << "bminimize : " << BddCountNodes(p, x);
  if(etotal) {
    int error = BddOr(p, BddAnd(p, eonset, LitNot(x)), BddAnd(p, eoffset, x));
    std::cout << " (" << 100 * (1 - ((double)BddCountOnes(p, error) / etotal)) << "%)";
  }
  std::cout << std::endl;
  
  aig = GenAig( p, x );
  
  aig->write(aigname);

  delete aig;
  BddManFree(p);
}

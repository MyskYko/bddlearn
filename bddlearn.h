#pragma once

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <string>
#include <vector>
#include <map>
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
    unsigned           nUniqueMask;   // selection mask for unique table
    unsigned           nCacheMask;    // selection mask for computed table
    int                nCacheLookups; // the number of computed table lookups
    int                nCacheMisses;  // the number of computed table misses
};

int Var2Lit( int i, bool c ) { return i << 1 + (int)c; }
int Lit2Var( int i ) { return i >> 1; }
int LitIsCompl( int i ) { return i & 1; }
int LitRegular( int i ) { return i & ~1; }
int LitNot( int i ) { return i ^ 1; }
int LitNotCond( int i, bool c ) { return i ^ (int)c; }

int BddIthVar( int i ) { return Var2Lit(i + 1, 0); }
unsigned BddHash( int Arg0, int Arg1, int Arg2 ) { return 12582917 * Arg0 + 4256249 * Arg1 + 741457 * Arg2; }

int BddVar( BddMan * p, int i ) { return (int)p->pVars[Lit2Var(i)]; }
int BddThen( BddMan * p, int i ) { return LitNotCond(p->pObjs[LitRegular(i)], LitIsCompl(i)); }
int BddElse( BddMan * p, int i ) { return LitNotCond(p->pObjs[LitRegular(i)+1], LitIsCompl(i)); }

int BddMark( BddMan * p, int i ) { return (int)p->pMark[Lit2Var(i)]; }
void BddSetMark( BddMan * p, int i, int m ){ p->pMark[Lit2Var(i)] = m; }

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
    assert( Var < BddVar(p, Then)  );
    assert( Var < BddVar(p, Else) );
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
    p->pVars[0]    = 0xffff;
    p->nObjs       = 1;
    for ( i = 0; i < nVars; i++ )
        BddUniqueCreate( p, i, 1, 0 );
    assert( p->nObjs == nVars + 1 );
    return p;
}
void BddManFree( BddMan * p )
{
    printf( "BDD stats: Var = %d  Obj = %d  Alloc = %d  Hit = %d  Miss = %d  ", 
        p->nVars, p->nObjs, p->nObjsAlloc, p->nCacheLookups-p->nCacheMisses, p->nCacheMisses );
    free( p->pUnique );
    free( p->pNexts );
    free( p->pCache );
    free( p->pObjs );
    free( p->pVars );
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
    int r0, r1, r;
    if ( a == 0 ) return 0;
    if ( b == 0 ) return 0;
    if ( a == 1 ) return b;
    if ( b == 1 ) return a;
    if ( a == b ) return a;
    if ( a > b )  return BddAnd( p, b, a );
    if ( (r = BddCacheLookup(p, a, b)) >= 0 )
        return r;
    if ( BddVar(p, a) < BddVar(p, b) )
        r0 = BddAnd( p, BddElse(p, a), b ), 
        r1 = BddAnd( p, BddThen(p, a), b );
    else if ( BddVar(p, a) > BddVar(p, b) )
        r0 = BddAnd( p, a, BddElse(p, b) ), 
        r1 = BddAnd( p, a, BddThen(p, b) );
    else // if ( BddVar(p, a) == BddVar(p, b) )
        r0 = BddAnd( p, BddElse(p, a), BddElse(p, b) ), 
        r1 = BddAnd( p, BddThen(p, a), BddThen(p, b) );
    r = BddUniqueCreate( p, std::min(BddVar(p, a), BddVar(p, b)), r1, r0 );
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
    if ( BddVar(p, f) > BddVar(p, c) )
      return BddRestrict( p, f, BddOr( p, BddElse(p, c), BddThen(p, c) ) );
    if ( BddVar(p, f) < BddVar(p, c) )
        r0 = BddRestrict( p, BddElse(p, f), c ),
        r1 = BddRestrict( p, BddThen(p, f), c );
    else
        r0 = BddRestrict( p, BddElse(p, f), BddElse(p, c) ),
        r1 = BddRestrict( p, BddThen(p, f), BddThen(p, c) );
    return BddUniqueCreate( p, std::min(BddVar(p, f), BddVar(p, c)), r1, r0 );
}

/**Function*************************************************************
  Synopsis    [trial of minimization between onset and offset]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddMinimize( BddMan * p, int on, int off )
{
    int r0, r1;
    if ( on == off ) return -1;
    if ( on == 1 ) return 1;
    if ( off == 1 ) return 0;
    if ( on == 0 ) return LitNot(off);// 0
    if ( off == 0 ) return on; // 1
    if ( BddVar(p, on) < BddVar(p, off) )
        r0 = BddMinimize( p, BddElse(p, on), off ), 
        r1 = BddMinimize( p, BddThen(p, on), off );
    else if ( BddVar(p, on) > BddVar(p, off) )
        r0 = BddMinimize( p, on, BddElse(p, off) ), 
        r1 = BddMinimize( p, on, BddThen(p, off) );
    else // if ( BddVar(p, on) == BddVar(p, off) )
        r0 = BddMinimize( p, BddElse(p, on), BddElse(p, off) ), 
        r1 = BddMinimize( p, BddThen(p, on), BddThen(p, off) );
    if ( r0 == -1 && r1 == -1 ) return -1;
    if ( r0 == -1 ) r0 = LitNot(r1);//return r1;
    if ( r1 == -1 ) r1 = LitNot(r0);//return r0;
    return BddUniqueCreate( p, std::min(BddVar(p, on), BddVar(p, off)), r1, r0 );
}

uint64_t BddMinimize2( BddMan * p, int on, int off )
{
    uint64_t r0, r1;
    // question ... is it ok to assign f to 0?
    if ( on == off ) return 1ull << 32;
    if ( on == 1 ) return 1;
    if ( off == 1 ) return 0;
    if ( on == 0 ) return (uint64_t)LitNot(off) << 32;
    if ( off == 0 ) return ((uint64_t)LitNot(on) << 32) + 1;
    if ( BddVar(p, on) < BddVar(p, off) )
        r0 = BddMinimize2( p, BddElse(p, on), off ), 
        r1 = BddMinimize2( p, BddThen(p, on), off );
    else if ( BddVar(p, on) > BddVar(p, off) )
        r0 = BddMinimize2( p, on, BddElse(p, off) ), 
        r1 = BddMinimize2( p, on, BddThen(p, off) );
    else // if ( BddVar(p, on) == BddVar(p, off) )
        r0 = BddMinimize2( p, BddElse(p, on), BddElse(p, off) ), 
        r1 = BddMinimize2( p, BddThen(p, on), BddThen(p, off) );
    uint r0f, r0g, r1f, r1g;
    r0f = r0;
    r0g = r0 >> 32;
    r1f = r1;
    r1g = r1 >> 32;
    uint64_t rg = BddUniqueCreate( p, std::min(BddVar(p, on), BddVar(p, off)), r1g, r0g );
    rg = rg << 32;
    int f = BddXor( p, r0f, r1f );
    int g = BddOr( p, r0g, r1g );
    int neq = BddOr( p, f, g );
    if( neq == 1 ) {
      int lr0 = BddAnd( p, LitNot(r0f), LitNot(r0g) );
      int lr1 = BddAnd( p, r1f, LitNot(r1g) );
      int l = BddOr( p, lr0, lr1 );
      /*
      int ur0 = BddOr( p, LitNot(r0f), r0g );
      int ur1 = BddOr( p, r1f, r1g );
      int u = BddAnd( p, ur0, ur1 );
      */
      int r = l; // l, r, or between l and u
      return rg + BddUniqueCreate( p, std::min(BddVar(p, on), BddVar(p, off)), r, LitNot(r) );
    }
    int eq = BddOr( p, LitNot( f ), g );
    if( eq == 1 ) {
      int lr0 = BddAnd( p, r0f, LitNot(r0g) );
      int lr1 = BddAnd( p, r1f, LitNot(r1g) );
      int l = BddOr( p, lr0, lr1 );
      /*
      int ur0 = BddOr( p, r0f, r0g );
      int ur1 = BddOr( p, r1f, r1g );
      int u = BddAnd( p, ur0, ur1 );
      */
      int r = l; // l, r, or between l and u
      return rg + r;
    }
    return rg + BddUniqueCreate( p, std::min(BddVar(p, on), BddVar(p, off)), r1f, r0f );
}

/**Function*************************************************************
  Synopsis    [traditional squeeze between l (lower) and u (upper) bound]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddSqueeze( BddMan * p, int l, int u )
{
  if (l == 0) return l;
  if (u == 1) return u;
  int topu, topl, index, le, lt, ue, ut;
  topu = BddVar( p, u );
  topl = BddVar( p, l );
  if ( topu <= topl ) {
    index = topu;
    ut = BddThen( p, u ); ue = BddElse( p, u );
  } else {
    index = topl;
    ut = ue = u;
  }
  if ( topl <= topu ) {
    lt = BddThen( p, l ); le = BddElse( p, l );
  } else {
    lt = le = l;
  }
  int r;
  if ( BddOr( p, LitNot(lt), le ) == 1 && BddOr( p, LitNot(ue), ut ) == 1 )
    return BddSqueeze( p, le, ue );
  if ( BddOr( p, LitNot(le), lt ) == 1 && BddOr( p, LitNot(ut), ue ) == 1 )
    return BddSqueeze( p, lt, ut );
  if ( BddOr( p, LitNot(le), LitNot(ut) ) == 1 && BddOr( p, ue, lt ) == 1 ) {
    r = BddSqueeze( p, lt, ut );
    return BddUniqueCreate( p, index, r, LitNot(r) );
  }
  if ( BddOr( p, LitNot(lt), LitNot(ue) ) == 1 && BddOr( p, ut, le ) == 1 ) {
    r = BddSqueeze( p, le, ue );
    return BddUniqueCreate( p, index, LitNot(r), r );
  }
  int ar = -1;
  if ( BddOr( p, LitNot(lt), ue ) == 1 && BddOr( p, LitNot(le), ut ) == 1 ) {
    int au, al;
    au = BddAnd( p, ut, ue );
    al = BddOr( p , lt, le );
    ar = BddSqueeze( p, al, au );
  }
  int t, e;
  t = BddSqueeze( p, lt, ut );
  e = BddSqueeze( p, le, ue );
  r = (t == e) ? t : BddUniqueCreate( p, index, t, e );
  if ( ar != -1 )
    if ( BddCountNodes( p,ar ) <= BddCountNodes( p, r ) )
      r = ar;
  return r;
}

/**Function*************************************************************
  Synopsis    [small intersect between two functions with DC]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
int BddDCIntersect( BddMan * p, int af, int ag, int bf, int bg )
{
  // terminal (care set)
  if(ag == 0 && bg == 0) assert(af == bf);
  if(ag == 0) return af;
  if(bg == 0) return bf;
  // terminal (DC)
  if(ag == 1 && bg == 1) return 0;
  if(ag == 1) return bf;
  if(bg == 1) return af;
  // top var
  int var = std::min({BddVar(p, af), BddVar(p, ag), BddVar(p, bf), BddVar(p, bg)});
  int af0, af1, ag0, ag1, bf0, bf1, bg0, bg1;
  if(var == BddVar(p, af)) af0 = BddElse(p, af), af1 = BddThen(p, af);
  else af0 = af1 = af;
  if(var == BddVar(p, ag)) ag0 = BddElse(p, ag), ag1 = BddThen(p, ag);
  else ag0 = ag1 = ag;
  if(var == BddVar(p, bf)) bf0 = BddElse(p, bf), bf1 = BddThen(p, bf);
  else bf0 = bf1 = bf;
  if(var == BddVar(p, bg)) bg0 = BddElse(p, bg), bg1 = BddThen(p, bg);
  else bg0 = bg1 = bg;
  // only one case is cared
  if(ag0 == 1 && bg0 == 1)
    return BddDCIntersect(p, af1, ag1, bf1, bg1);
  if(ag1 == 1 && bg1 == 1)
    return BddDCIntersect(p, af0, ag0, bf0, bg0);
  // recurse for each case
  int r0, r1;
  r0 = BddDCIntersect(p, af0, ag0, bf0, bg0);
  r1 = BddDCIntersect(p, af1, ag1, bf1, bg1);
  // compute DC set for each case
  int rg0, rg1;
  rg0 = BddAnd(p, ag0, bg0);
  rg1 = BddAnd(p, ag1, bg1);
  // check if intersection exists
  int f, g;
  f = BddXor(p, r0, r1);
  g = BddOr(p, rg0, rg1);
  // then, recurse for small intersection
  if(BddOr(p, LitNot(f), g) == 1)
    return BddDCIntersect(p, r0, rg0, r1, rg1);
  if(BddOr(p, f, g) == 1) {
    int r = BddDCIntersect(p, LitNot(r0), rg0, r1, rg1);
    return BddUniqueCreate( p, var, r, LitNot(r) );
  }
  // else, return with a new node
  return BddUniqueCreate( p, var, r1, r0 );  
}

/**Function*************************************************************
  Synopsis    [main]
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
void bddlearn(std::vector<boost::dynamic_bitset<> > const & inputs, boost::dynamic_bitset<> const & output, std::string aigname) {
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

  std::cout << "onset : " << BddCountNodes(p, onset) << std::endl;
  std::cout << "offset : " << BddCountNodes(p, offset) << std::endl;

  aigman * aig;
  
  /*
  int y = BddSqueeze(p, onset, LitNot(offset));
  std::cout << "squeeze : " << BddCountNodes(p, y) << std::endl;
  aig = GenAig( p, y );
  */

  int x = BddDCIntersect(p, onset, LitNot(onset), LitNot(offset), LitNot(offset));
  std::cout << "dcinter : " << BddCountNodes(p, x) << std::endl;
  aig = GenAig( p, x );
  
  aig->write(aigname);

  delete aig;
  BddManFree(p);
}

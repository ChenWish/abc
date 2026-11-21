/**************************************************************************************************
GipSAT -- C port of the GipSAT solver from the rIC3 model checker (https://github.com/gipsyh/rIC3),
ported from rIC3 v1.5.2-60-g4a97bec, src/gipsat/.
Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved.
Ported to C for ABC by Wish, 2026.

rIC3 is distributed under the GNU General Public License v3. This port is distributed as part of
ABC under the ABC license (see copyright.txt in the ABC root) with the explicit permission of the
rIC3 author.
**************************************************************************************************/

#include <math.h>
#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

// internal search result: the per-round conflict budget was exhausted
#define GIP_RESTART (-2)

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void Gip_SolverNewLevel( Gip_Solver_t * p )
{
    Vec_IntPush( p->vPosInTrail, Vec_IntSize(p->vTrail) );
}

/**Function*************************************************************

  Synopsis    [Reconsiders deferred decisions when watched clauses can become active.]

  Description []

***********************************************************************/
// A skipped variable stays on this list until backtracking. New watches wake
// individual variables; backtracking wakes all of them because satisfied
// clauses can lose their satisfying assignment. No clause is removed.
void Gip_SolverWakeSkipped( Gip_Solver_t * p, int fVsids )
{
    int Var;
    if ( !p->fJustify ) return;
    while ( Vec_IntSize(p->vJustSkip) )
    {
        Var = Vec_IntPop( p->vJustSkip );
        if ( fVsids && p->pValue[Var] == GIP_NONE && Gip_DomainHas(&p->Domain, Var) )
            Gip_VsidsPush( &p->Vsids, Var );
        p->pJustSkip[Var] = 0;
    }
}

/**Function*************************************************************

  Synopsis    [Tests whether a clause already holds or lies outside the query domain.]

  Description []

***********************************************************************/
static int Gip_SolverClauseSatisfiedOrOutside( Gip_Solver_t * p, int Cref )
{
    int i, Lit, * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    int nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    for ( i = 0; i < nLits; i++ )
    {
        Lit = pLits[i];
        if ( Gip_SolverLitValue(p, Lit) == GIP_TRUE ||
             (Gip_SolverLitValue(p, Lit) == GIP_NONE && !Gip_DomainHas(&p->Domain, Gip_LitVar(Lit))) )
            return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Checks whether a variable's watched clauses still require a decision.]

  Description []

***********************************************************************/
int Gip_SolverCanSkipDecision( Gip_Solver_t * p, int Var )
{
    int k, i;
    p->nJustChecks++;
    for ( k = 0; k < 2; k++ )
    {
        Gip_WVec_t * pW = &p->pWatchers[2*Var+k];
        for ( i = 0; i < pW->nSize; i++ )
            if ( Gip_SolverLitValue(p, pW->pArray[i].blocker) != GIP_TRUE &&
                 !Gip_SolverClauseSatisfiedOrOutside(p, Gip_WatchRef(pW->pArray[i].clause)) )
                return 0;
    }
    if ( !p->pJustSkip[Var] )
        Vec_IntPush( p->vJustSkip, Var );
    p->pJustSkip[Var] = 1;
    p->nJustSkipped++;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks that the returned partial assignment justifies the query.]

  Description []

***********************************************************************/
void Gip_SolverCheckPartialModel( Gip_Solver_t * p, int * pAssump, int nAssump )
{
    Vec_Int_t * vLists[4] = { p->Cdb.vTrans, p->Cdb.vLemmas, p->Cdb.vLearnt, p->Cdb.vTemp };
    int k, i, Cref;
    for ( i = 0; i < nAssump; i++ )
        assert( Gip_SolverLitValue(p, pAssump[i]) == GIP_TRUE );
    for ( k = 0; k < 4; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
                assert( Gip_SolverClauseSatisfiedOrOutside(p, Cref) );
}

/**Function*************************************************************

  Synopsis    [Backtracks to the given level, saving phases.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
// the dirty bits of the incremental lemma cover (see Gip_IncNextDirty)
static inline int Gip_IncIsDirty( Gip_Solver_t * p, int pos )
{
    return (int)((p->Jftr.pIncDirty[pos >> 6] >> (pos & 63)) & 1);
}
static inline void Gip_IncSetDirty( Gip_Solver_t * p, int pos )
{
    word * pW = p->Jftr.pIncDirty + (pos >> 6);
    if ( (*pW >> (pos & 63)) & 1 )
        return;
    *pW |= (word)1 << (pos & 63);
    p->Jftr.pIncSum[pos >> 12] |= (word)1 << ((pos >> 6) & 63);
}
static inline void Gip_IncClearDirty( Gip_Solver_t * p, int pos )
{
    word * pW = p->Jftr.pIncDirty + (pos >> 6);
    *pW &= ~((word)1 << (pos & 63));
    if ( *pW == 0 )
        p->Jftr.pIncSum[pos >> 12] &= ~((word)1 << ((pos >> 6) & 63));
}

// An exit that the invariants of the mode exclude: a clause found falsified although the propagation reported no conflict, the lemma
// cover out of step with the lemma clauses, a node that stays open, a decision on a var outside the domain, a failed check of an
// early answer. The solver state cannot be trusted at such a point (continuing with the plain search from it would hide the cause
// and could return a wrong answer), so no answer is given and the run stops.
static void Gip_JftrFatal( Gip_Solver_t * p, const char * pWhat )
{
    Abc_Print( 1, "jftr: internal error: %s (solve %lld, level %d, trail %d, domain %d). No answer is given from this state.\n",
        pWhat, (long long)p->Stats.nSolves, Gip_SolverLevelOf(p), Vec_IntSize(p->vTrail), Vec_IntSize(p->Domain.Set.vSet) );
    fflush( stdout );
    fprintf( stderr, "jftr: internal error: %s\n", pWhat );
    abort();
}
// the jftr decision just made at the current level (step: 0 gate, 1 constraint clause, 2 lemma clause)
static inline void Gip_JftrNoteDecision( Gip_Solver_t * p, int Lit, int Step )
{
    int Level = Gip_SolverLevelOf( p ), Kind = p->pCtx->pKind[Gip_LitVar(Lit)];
    // the invariant of the early stop: a decision never assigns a var outside the domain -- the propagation does not enforce the
    // clauses over such a var, and the root nodes are selected by the clauses whose unassigned literals are all in the domain
    if ( !Gip_DomainHas( &p->Domain, Gip_LitVar(Lit) ) )
    {
        Abc_Print( 1, "jftr: decision outside the domain: step %d var %d kind %d level %d assumptions %d fixed domain %d\n", Step, Gip_LitVar(Lit), Kind, Level, p->Jftr.nAssump, p->fTempDomain );
        Gip_JftrFatal( p, "a decision on a variable outside the domain" );
    }
}

void Gip_SolverBacktrack( Gip_Solver_t * p, int Level, int fVsids )
{
    if ( Gip_SolverLevelOf(p) <= Level )
    {
        Gip_SolverWakeSkipped( p, fVsids );
        return;
    }
    p->Jftr.fWalkClosed = 0;
    p->Jftr.nVerified = 0;  p->Jftr.iVerStart = p->Jftr.iLo;
    if ( Vec_IntSize(p->Jftr.vIncVol) > 0 )
    {
        // (the incremental lemma cover) a witness true on the trail but not in pM may be unassigned now
        int i, pos;
        Vec_IntForEachEntry( p->Jftr.vIncVol, pos, i )
            if ( pos < Vec_IntSize(p->Cdb.vLemmas) )
                Gip_IncSetDirty( p, pos );
        Vec_IntClear( p->Jftr.vIncVol );
    }
    // in jftr mode the VSIDS queue is not consumed, so nothing has to be put back
    if ( p->Jftr.fActive )
        fVsids = 0;
    while ( Vec_IntSize(p->vTrail) > Vec_IntEntry(p->vPosInTrail, Level) )
    {
        int Lit = Vec_IntPop( p->vTrail );
        int Var = Gip_LitVar( Lit );
        Gip_SolverSetNone( p, Var );
        if ( fVsids )
            Gip_VsidsPush( &p->Vsids, Var );
        if ( !p->Jftr.fActive )   // the jftr part of a solve leaves the saved phases alone
            p->pPhase[Var] = (char)(1 ^ Gip_LitCompl(Lit));
    }
    p->nPropagated = Vec_IntEntry( p->vPosInTrail, Level );
    Vec_IntShrink( p->vPosInTrail, Level );
    Gip_SolverWakeSkipped( p, fVsids );
    if ( p->Jftr.iScan > Vec_IntSize(p->vTrail) )
        p->Jftr.iScan = Vec_IntSize( p->vTrail );
    // a node below the backtrack point may have been justified by a popped literal: recheck from level 1
    if ( p->Jftr.fActive )
    {
        p->Jftr.iCheck = Gip_SolverLevelOf(p) > 0 ? Vec_IntEntry( p->vPosInTrail, 0 ) : Vec_IntSize( p->vTrail );
        p->Jftr.fRootRecheck = 1;   // a root node may have been closed by a popped literal too
        Vec_IntClear( p->Jftr.vFront );   // every node that can be open is queued again by the next scan: the root nodes and the trail above level 0
    }
}

/**Function*************************************************************

  Synopsis    [One restart round of CDCL search.]

  Description [Returns GIP_SAT/GIP_UNSAT when decided, GIP_RESTART when
  the per-round conflict budget (noc) is exhausted, GIP_UNDEF when a
  global limit (conflicts/time) canceled the solve.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gip_JftrOpenClause( Gip_Solver_t * p, int Var );
static int Gip_JftrOpenClauseDom( Gip_Solver_t * p, int Var );
// debug check (PDR2_JFTR_CHECK): the transition part of the contract of an early answer -- the assigned nodes stay consistent with
// their definitions whatever values the unassigned leaves take. That holds when every assigned node of the domain is closed (each of
// its defining clauses has a true literal), the root facts included. (The lemma clauses are a separate matter: they hold in the one
// register completion of the answer, see Gip_JftrVerifyModel.)
static void Gip_JftrVerifyEarly( Gip_Solver_t * p )
{
    char * pKind = p->pCtx->pKind;
    int i, Lit, Var, nRoot = 0, nUpper = 0, iRootEnd = Gip_SolverLevelOf(p) > 0 ? Vec_IntEntry( p->vPosInTrail, 0 ) : Vec_IntSize( p->vTrail );
    p->Jftr.Ver.nEarly++;
    Vec_IntForEachEntry( p->vTrail, Lit, i )
    {
        Var = Gip_LitVar( Lit );
        if ( Var >= p->nVars || (pKind[Var] != GIP_KIND_NODE && pKind[Var] != GIP_KIND_CO) || p->pCtx->pCnf->pObj2Count[Var] == 0 )
            continue;
        if ( Gip_JftrOpenClause( p, Var ) < 0 )
            continue;
        if ( Gip_JftrOpenClauseDom( p, Var ) < 0 )
        {
            p->Jftr.Ver.nEarlyOut++;   // open only in clauses that have an unassigned literal outside the domain: not active for the plain search either
            continue;
        }
        if ( i < iRootEnd ) nRoot++; else nUpper++;
    }
    if ( nRoot || nUpper )
        Gip_JftrFatal( p, "PDR2_JFTR_CHECK: an early answer has an assigned node with an open defining clause" );
}

// debug check (PDR2_JFTR_CHECK=2): an independent check of the early answer. The unassigned inputs and registers of the domain get
// values (three patterns: saved phase, all false, all true), the unassigned nodes of the domain are evaluated from their fanins in
// var order with the static clauses, and then every clause is evaluated directly: the static transition clauses of every var that
// has a value, the lemma clauses, the constraint clauses of the round and (as a consistency test) the learnt clauses. A clause with
// a literal that still has no value (a var outside the domain) is not checked, as the plain search does not enforce it either.
// The constraint clauses left to a free register outside the domain are among those, so every constraint clause of the round
// (vCst, as Gip_JftrDecideCst reads them) is also checked by itself: it has a literal that is true now, or an unassigned
// register literal outside the domain that is recorded in vCstFree, and that literal must be true in pM (the completion
// the answer stands for).
// Nothing here uses the functions of the jftr decision.
static int Gip_VerLit( Gip_Solver_t * p, char * pVal, int Lit )
{
    int Var = Gip_LitVar( Lit ), v = Var < p->nVars ? pVal[Var] : p->pValue[Var];
    return v == GIP_NONE ? GIP_NONE : (v == GIP_TRUE) != Gip_LitCompl(Lit) ? GIP_TRUE : GIP_FALSE;
}
static int Gip_VerClause( Gip_Solver_t * p, char * pVal, int * pLits, int nLits )   // 1 = has a true literal, 0 = all false, -1 = not checked
{
    int k, fNone = 0;
    for ( k = 0; k < nLits; k++ )
    {
        int v = Gip_VerLit( p, pVal, pLits[k] );
        if ( v == GIP_TRUE )
            return 1;
        fNone |= v == GIP_NONE;
    }
    return fNone ? -1 : 0;
}
static void Gip_JftrVerifyModel( Gip_Solver_t * p )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    char * pKind = p->pCtx->pKind;
    char * pVal = ABC_ALLOC( char, p->nVars );
    Vec_Int_t * vDom = Vec_IntDup( p->Domain.Set.vSet );
    int Pat, i, k, Var, c, Cref, Lit, nFreeBad = 0, nPats = 3;
    Vec_IntSort( vDom, 0 );
    Vec_IntForEachEntry( p->Jftr.vCst, Cref, i )
    {
        int * pLits, nLits, fOk = 0;
        if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
            continue;
        pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );  nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
        for ( k = 0; k < nLits && !fOk; k++ )
            fOk = Gip_SolverLitValue(p, pLits[k]) == GIP_TRUE;
        for ( k = 0; k < nLits && !fOk; k++ )
        {
            Lit = pLits[k];  Var = Gip_LitVar( Lit );
            if ( Var >= p->nVars || pKind[Var] != GIP_KIND_LO || Gip_SolverLitValue(p, Lit) != GIP_NONE || Gip_DomainHas(&p->Domain, Var) || Vec_IntFind(p->Jftr.vCstFree, Lit) < 0 )
                continue;
            fOk = p->Jftr.pM[p->pCtx->pLoIdx[Var]] == (Gip_LitCompl(Lit) ? GIP_FALSE : GIP_TRUE);
        }
        nFreeBad += !fOk;
    }
    for ( Pat = 0; Pat < nPats; Pat++ )
    {
        int nBad = nFreeBad;
        memcpy( pVal, p->pValue, p->nVars );
        Vec_IntForEachEntry( vDom, Var, i )
        {
            int Raw;
            if ( Var >= p->nVars )
                continue;
            Raw = pVal[Var];
            if ( Raw != GIP_NONE )
                continue;
            if ( pKind[Var] == GIP_KIND_LO )
                pVal[Var] = p->Jftr.pM[p->pCtx->pLoIdx[Var]];   // the answer stands for this completion of the registers; the inputs stay free
            else if ( pKind[Var] == GIP_KIND_PI )
                pVal[Var] = Pat % 3 == 0 ? (p->pPhase[Var] == GIP_TRUE ? GIP_TRUE : GIP_FALSE) : Pat % 3 == 1 ? GIP_FALSE : GIP_TRUE;
            else if ( (pKind[Var] == GIP_KIND_NODE || pKind[Var] == GIP_KIND_CO) && pCnf->pObj2Count[Var] > 0 )
            {
                // the value for which every defining clause holds (the fanins have lower var numbers and have values by now)
                int v, fDone = 0, fUnknown = 0, fInside = 0, c0 = pCnf->pObj2Clause[Var], c1 = c0 + pCnf->pObj2Count[Var];
                // every fanin must have a value: a fanin without one is outside the domain -- then the node is not evaluated, which is
                // reported -- or inside it, which is a failure of the evaluation order
                for ( c = c0; c < c1; c++ )
                {
                    int * pLit;
                    for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
                    {
                        if ( Gip_LitVar(*pLit) != Var && Gip_VerLit( p, pVal, *pLit ) == GIP_NONE )
                        {
                            fUnknown = 1;
                            fInside |= Gip_DomainHas( &p->Domain, Gip_LitVar(*pLit) );
                        }
                    }
                }
                if ( fUnknown )
                {
                    // a fanin without a value inside the domain is a failure of the evaluation
                    if ( fInside ) nBad++;
                    else p->Jftr.Ver.nModelOut++;
                    continue;
                }
                for ( v = GIP_FALSE; v <= GIP_TRUE && !fDone; v++ )
                {
                    int fOk = 1;
                    pVal[Var] = (char)v;
                    for ( c = c0; c < c1 && fOk; c++ )
                        fOk = Gip_VerClause( p, pVal, pCnf->pClauses[c], (int)(pCnf->pClauses[c+1] - pCnf->pClauses[c]) ) == 1;
                    fDone = fOk;
                }
                if ( !fDone )
                {
                    // no value satisfies the defining clauses: the completion is not a model
                    pVal[Var] = (char)Raw;
                    nBad++;
                }
            }
        }
        for ( Var = 0; Var < p->nVars; Var++ )
        {
            int c0, c1;
            if ( pVal[Var] == GIP_NONE || (pKind[Var] != GIP_KIND_NODE && pKind[Var] != GIP_KIND_CO) || pCnf->pObj2Count[Var] == 0 )
                continue;
            c0 = pCnf->pObj2Clause[Var];  c1 = c0 + pCnf->pObj2Count[Var];
            for ( c = c0; c < c1; c++ )
                if ( Gip_VerClause( p, pVal, pCnf->pClauses[c], (int)(pCnf->pClauses[c+1] - pCnf->pClauses[c]) ) == 0 )
                    nBad++;
        }
        Vec_IntForEachEntry( p->Cdb.vLemmas, Cref, k )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) && Gip_VerClause( p, pVal, Gip_ClaLits(&p->Cdb.Alloc, Cref), Gip_ClaLen(&p->Cdb.Alloc, Cref) ) == 0 )
                nBad++;
        Vec_IntForEachEntry( p->Jftr.vCst, Cref, k )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) && Gip_VerClause( p, pVal, Gip_ClaLits(&p->Cdb.Alloc, Cref), Gip_ClaLen(&p->Cdb.Alloc, Cref) ) == 0 )
                nBad++;
        {
            // the learnt clauses: the plain ones, and the temporary ones with the activation literal, which are the temporary
            // clauses other than the round's constraint clauses
            Vec_Int_t * vLists[2] = { p->Cdb.vLearnt, p->Cdb.vTemp };
            int iList;
            for ( iList = 0; iList < 2; iList++ )
                Vec_IntForEachEntry( vLists[iList], Cref, k )
                    if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) && (iList == 0 || Vec_IntFind(p->Jftr.vCst, Cref) < 0) &&
                         Gip_VerClause( p, pVal, Gip_ClaLits(&p->Cdb.Alloc, Cref), Gip_ClaLen(&p->Cdb.Alloc, Cref) ) == 0 )
                        nBad++;
        }
        for ( k = 0; k < p->Jftr.nAssump; k++ )
            if ( Gip_VerLit( p, pVal, p->Jftr.pAssump[k] ) != GIP_TRUE )
                nBad++;
        p->Jftr.Ver.nModel++;
        if ( nBad > 0 )
            Gip_JftrFatal( p, "PDR2_JFTR_CHECK=2: a completion of an early answer violates a clause" );
    }
    Vec_IntFree( vDom );
    ABC_FREE( pVal );
}

// the budget of the mode ran out: its decisions are undone and the plain search goes on from the assumptions (Level = their number).
// The decision queue is then made what the plain search expects at that point. The mode never pops the queue (its decisions do not
// use it) and its backtracks push nothing back, so the queue still holds what it held at the start of the solve (empty after
// Gip_SolverNewRound, or the queue of a fixed MIC domain, which the mode's backtracks did not change either); the plain search
// expects it prepared once all assumptions are placed (Gip_SolverSearch prepares it after the last one, Gip_SolverSearchWithRestart
// before the search when there is none). The budget is tested only after every assumption is placed, so the level here is always
// the number of assumptions, also zero for a query without assumptions, and the queue is prepared here in every case: upstream's
// preparation for assumption-free queries is kept in effect for the plain part of the solve (with a fixed MIC domain the
// preparation is a no-op, as in the plain search: the queue was filled when the domain was set).
static void Gip_JftrHandOver( Gip_Solver_t * p, int Level )
{
    Gip_SolverBacktrack( p, Level, 0 );
    p->Jftr.fActive = 0;
    assert( Gip_SolverLevelOf(p) == p->Jftr.nAssumpCur );
    Gip_SolverPrepareVsids( p );
}

static int Gip_SolverSearch( Gip_Solver_t * p, int * pAssump, int nAssump, double noc )
{
    double numConflict = 0.0;
    while ( 1 )
    {
        int Conflict = Gip_SolverPropagate( p );
        if ( Conflict != GIP_CREF_NONE )
        {
            int btl;
            numConflict += 1.0;
            p->Stats.nConflicts++;
            if ( Gip_SolverLevelOf(p) == 0 )
            {
                Gip_LitSetClear( &p->UnsatCore );
                p->fTrivialUnsat = 1;
                p->iTrivialFrame = p->iCoreFrame = Gip_SolverConflictFrame( p, Conflict );
                return GIP_UNSAT;
            }
            btl = Gip_SolverAnalyze( p, Conflict, p->vLearntCls );
            Gip_SolverBacktrack( p, btl, 1 );
            if ( Vec_IntSize(p->vLearntCls) == 1 )
            {
                assert( btl == 0 );
                Gip_SolverAssign( p, Vec_IntEntry(p->vLearntCls, 0), GIP_CREF_NONE );
                p->pTag0[Gip_LitVar(Vec_IntEntry(p->vLearntCls, 0))] = p->iAnaFrame;
            }
            else
            {
                int Kind = GIP_CLA_LEARNT, i, Lit, Cref;
                Vec_IntForEachEntry( p->vLearntCls, Lit, i )
                    if ( Gip_LitVar(Lit) == p->constrainAct )
                        Kind = GIP_CLA_TEMPORARY;
                Cref = Gip_SolverAttachClauseTag( p, Vec_IntArray(p->vLearntCls), Vec_IntSize(p->vLearntCls), Kind, (unsigned)p->iAnaFrame << 1 );
                Gip_CdbBump( &p->Cdb, Cref );
                Gip_SolverAssign( p, Gip_ClaLits(&p->Cdb.Alloc, Cref)[0], Cref );
            }
            Gip_VsidsDecay( &p->Vsids );
            Gip_CdbDecay( &p->Cdb );
        }
        else
        {
            if ( (p->nConfLimit > 0 && p->Stats.nConflicts >= p->nConfCounted + p->nConfLimit) ||
                 (p->nPropLimit > 0 && p->Stats.nPropagations >= p->nPropLimit) ||
                 ((p->TimeLimit || p->pFuncStop) && p->Stats.nPropagations >= p->nTimeCheck && Gip_SolverTimedOut(p)) )
            {
                Gip_SolverBacktrack( p, nAssump, 1 );
                p->fCanceled = 1;
                return GIP_UNDEF;
            }
            if ( noc >= 0 && numConflict >= noc )
            {
                Gip_SolverBacktrack( p, nAssump, 1 );
                return GIP_RESTART;
            }
            Gip_SolverCleanLearnt( p, 0 );
            // place assumptions one decision level at a time
            while ( Gip_SolverLevelOf(p) < nAssump )
            {
                int a = pAssump[Gip_SolverLevelOf(p)];
                int v = Gip_SolverLitValue( p, a );
                if ( v == GIP_TRUE )
                {
                    Gip_SolverNewLevel( p );
                    if ( Gip_SolverLevelOf(p) == nAssump && !p->Jftr.fActive )
                        Gip_SolverPrepareVsids( p );
                }
                else if ( v == GIP_FALSE )
                {
                    Gip_SolverAnalyzeUnsatCore( p, a );
                    return GIP_UNSAT;
                }
                else
                {
                    Gip_SolverNewLevel( p );
                    Gip_SolverAssign( p, a, GIP_CREF_NONE );
                    if ( Gip_SolverLevelOf(p) == nAssump && !p->Jftr.fActive )
                        Gip_SolverPrepareVsids( p );
                    goto continue_main;
                }
            }
            if ( p->Jftr.fActive )
            {
                if ( p->Stats.nConflicts - p->nConfCounted >= p->Jftr.nConf )
                {
                    // the budget ran out: the rest of the solve is the plain VSIDS search, from the
                    // assumptions (the learnt clauses of the jftr part stay; the saved phases are as before it)
                    Gip_JftrHandOver( p, nAssump );
                    goto continue_main;
                }
                if ( !Gip_SolverDecideJftr( p ) )
                {
                    p->Jftr.fEarly = p->Jftr.fActive;
                    return GIP_SAT;
                }
            }
            else if ( !Gip_SolverDecide( p ) )
                return GIP_SAT;
        }
continue_main:;
    }
}

static double Gip_Luby( double y, unsigned x )
{
    unsigned size = 1, seq = 0;
    while ( size < x + 1 )
    {
        seq++;
        size = 2 * size + 1;
    }
    while ( size - 1 != x )
    {
        size = (size - 1) >> 1;
        seq--;
        x %= size;
    }
    return pow( y, (double)seq );
}

/**Function*************************************************************

  Synopsis    [Search with luby restarts.]

  Description [nRestartLimit < 0 means unlimited. After 10 restarts,
  switches from the approximate bucket to the exact activity heap.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverSearchWithRestart( Gip_Solver_t * p, int * pAssump, int nAssump, int nRestartLimit )
{
    unsigned restarts = 0;
    // With assumptions, Search prepares the decision queue after installing
    // the last one. An assumption-free query must prepare it here; otherwise
    // an empty queue can report SAT before deciding the permanent domain.
    // in jftr mode the queue is prepared when the mode hands over to the plain search, at level 0 for a query without assumptions,
    // see Gip_JftrHandOver; an early answer needs no queue
    if ( nAssump == 0 && !p->Jftr.fActive )
        Gip_SolverPrepareVsids( p );
    while ( 1 )
    {
        double restBase;
        int res;
        if ( nRestartLimit >= 0 && restarts >= (unsigned)nRestartLimit )
            return GIP_UNDEF;
        if ( restarts > 10 && p->Vsids.fEnableBucket )
        {
            int i, d;
            p->Vsids.fEnableBucket = 0;
            Gip_HeapClear( &p->Vsids.Heap );
            Vec_IntForEachEntry( p->Domain.Set.vSet, d, i )
                if ( p->pValue[d] == GIP_NONE )
                    Gip_VsidsPush( &p->Vsids, d );
        }
        restBase = Gip_Luby( 2.0, restarts );
        res = Gip_SolverSearch( p, pAssump, nAssump, restBase * 100.0 );
        if ( res == GIP_RESTART )
        {
            restarts++;
            continue;
        }
        return res;
    }
}

////////////////////////////////////////////////////////////////////////
///                      JFTR MODE                                   ///
////////////////////////////////////////////////////////////////////////

/*
   The decision rule of the jftr (justification frontier) mode is backward justification on the CNF of the circuit.
   GipSAT's CNF (Cnf_DeriveOther) has a variable for every AIG object; the mapped nodes (cut
   functions of up to a few leaves) and the outputs are the variables with defining clauses, the
   inputs and register outputs are the leaves. An assigned variable is justified when every
   defining clause that contains its now-false literal has another true literal: its value is
   then forced by its leaves whatever the unassigned leaves become. A clause that has no true
   literal is open (after propagation it has two or more unassigned literals); the decision picks
   one of its unassigned literals and makes it true.

   Early stop (the contract of an early SAT answer, before any shrink). The answer is a partial assignment such that
     (a) every assigned node of the formula the plain search enforces is closed: the nodes assigned above level 0 (kept on the
         frontier until none of their clauses is open) and the nodes assigned at level 0 that have an open clause whose
         unassigned literals are all in the domain (Gip_JftrRootUpdate);
     (b) every lemma clause has a register literal that is true under "the trail value, else pM" (Gip_JftrLitCovers), where
         pM is the register completion the solver keeps: the saved phases at first, then the values of the registers that
         each early answer assigned above level 0 (Gip_JftrCoverCommit) and the polarities recorded in vCstFree;
     (c) every constraint clause of the round has a true literal, or is left to an unassigned register outside the domain;
     (d) no assumption and no decision assigned a var outside the domain of the query above level 0 (the propagation skips
         clauses by the domain of their blocker, which is only sound while no such var is assigned above level 0).
   Then there is a completion that is a model of what the plain search enforces: the free inputs take any value, the registers
   recorded for the clauses of (c) the value that satisfies them (they are outside the cone of the query, so nothing else
   assigned depends on them; vCstFree keeps their polarities compatible), and the unassigned nodes the value of their
   function. The unassigned registers of the domain are not free: a lemma clause may be covered only by the value an unassigned
   register has in pM, so the answer stands for one completion of the registers, "the trail value, else pM"
   (Gip_SolverCoverValue). The transition clauses hold by (a), the lemma and
   constraint clauses by (b) and (c), the learnt clauses are consequences. The answer is relative to the domain: a clause
   with an unassigned literal outside it is ignored by the plain search as well. The answer and its completion are valid
   until the next solve starts or another operation changes the assignment or the formula.
   Facts about the caller that this relies on (not checked at run time): the only unit asserted from outside over a non-leaf
   var is the property, which the engine adds to a frame only after the bad-state query of that frame was UNSAT, so it follows
   from that frame's clauses (lemma clauses, initial-state units, with the level-0 facts they were simplified by) and the
   transition relation; units learnt later are consequences of the same; a constraint clause left to a free register is the
   "not full" clause of a parent cube in a nested generalization; the domain of the query is closed under dependency apart
   from vars assigned at level 0 (it is the seeds of the query and the vars of the lemma clauses, with their fanin cones),
   and every assumption is over a var of the domain or over a var that is already assigned at level 0 (a root fact).
   (a)-(d) establish the SAT answer, for every kind of query. A consumer that extracts a predecessor needs more and reads a
   different object: the justification walk from the assumptions (Gip_JftrWalk) selects leaves that imply the targets under
   the transition relation alone, and a shrink keeps only those. The walk is this transition-only certificate of the
   predecessor; it runs for the kinds whose model may become a predecessor (fLeaves), not for yes/no queries. Neither
   the answer nor the certificate rests on the lifting query of Pdr2_ManGetPred: that query is the engine's generalization
   of the predecessor, and it can be skipped (an empty cube, lifting switched off) or interrupted (a limit) without any loss.
   What each consumer of an early answer reads:
     yes/no kinds (push, propagation, ...)              nothing (the CTI cache of a propagation query stores the assigned
                                                        registers, and an unassigned register of the domain with its value in
                                                        pM: the cached state is the completion the answer stands for, read
                                                        right after the solve; an unassigned register outside the domain is
                                                        stored as unknown)
     predecessor of block / bad / CTG / inf / CTP       the leaves of the walk, through Pdr2_ManGetPred: the assigned inputs and,
                                                        as candidates of the lifting, the assigned registers of the cone (a
                                                        shrink leaves only leaves of the walk assigned above level 0)
     Down join, keep tests, recorded predecessor        Pdr2_ManVarValue (the trail value, else pM)
   The mode never answers UNSAT by itself: its decisions are ordinary decisions of the CDCL search. Any exit that these
   invariants exclude stops the run (Gip_JftrFatal).
   Where the mode is defined (a correctness boundary, not a tuning choice). The mode runs only in a solve whose caller requested it
   right before (Gip_SolverSetJftr; Gip_SolverSolve consumes the request, so every other solve is the plain search; a request made
   while a batch exists is ignored, because a resumed solve keeps a trail prefix and skips the round setup), and the caller
   requests it only for a solver that satisfies all of the following; for every other solver the plain search is used:
     the context: Cnf_DeriveOther's CNF as derived (fJftrCnf: no structural encoding, no variable elimination), var == AIG object id
       (no compact numbering, no alias of unused inputs) and no variable beyond the objects (no activation variables of a shared
       solver);
     the solver: an ordinary frame / infinity solver of its own (not a handle of a shared solver, not the shared solver, not a
       private bad-state solver that asserts the property as a unit), built by Gip_SolverNew (not lazily loaded, not a copy made by
       Gip_SolverCloneRoot, nothing imported by Gip_SolverWarmStartMode: fCopied), without clause recycling and without the
       plain search's own partial-model policies in the query (fJustify, fInputDecisions);
     the caller: no unit over a non-leaf var other than the property (no initial-state predicate and no trace guard over a
       register input), and the caller's consumers read the answer as described above.
   The propagators that skip watch lists by the domain (PDR2_SKIPWATCH, PDR2_PARTWATCH) need no hook of the mode: the mode neither
   moves watches nor changes the domain, and by (d) every var it assigns above level 0 is in the domain, so a skipped list (all of
   whose clauses have their blocker outside the domain, unassigned) is skipped by the mode's propagation for the same reason as by the
   plain search's. The packed domain bit (PDR2_PACKEDDOM) lives in pLitVal, and the watch-state domain (PDR2_WATCH_STATE) keeps
   the value in the membership byte: the mode reads values through Gip_SolverLitValue and membership through Gip_DomainHas, and
   it assigns and unassigns only through Gip_SolverAssign / Gip_SolverSetNone, which maintain both. The mode does not read watch
   lists, so the representation of the watches (inline binary clauses, packed storage) does not concern it.
*/

// per-var kind and controllability costs; pCc[4*v + 2*m + b] = cost of making var v take value b
// with metric m (0: registers that must be assigned, PI = 0 and LO = 1 per leaf, no gate cost;
// 1: classic SCOAP, every leaf 1 and every gate +1); for a node the cost of value b is the minimum
// over its defining clauses C containing the literal (v = b) of the sum over the other literals
// of the cost of making them false
#define GIP_CC_MAX (1 << 28)
static inline int Gip_CcLitTrue( int * pCc, int Lit, int m )  { return pCc[4 * Gip_LitVar(Lit) + 2 * m + (1 ^ Gip_LitCompl(Lit))]; }
void Gip_CtxPrepareJftr( Gip_Ctx_t * p )
{
    Cnf_Dat_t * pCnf = p->pCnf;
    Aig_Obj_t * pObj;
    int v, b, m, c;
    if ( p->pKind )
        return;
    // one extra entry: the solvers' activation var is nVars
    p->pKind  = ABC_CALLOC( char, p->nVars + 1 );
    p->pCc    = ABC_CALLOC( int, 4 * (p->nVars + 1) );
    p->pLoIdx = ABC_ALLOC( int, p->nVars + 1 );
    p->nLo    = 0;
    for ( v = 0; v < p->nVars; v++ )
    {
        pObj = Aig_ManObj( p->pAig, v );
        if ( pObj == NULL )
            p->pKind[v] = GIP_KIND_OTHER;
        else if ( Aig_ObjIsCo(pObj) )
            p->pKind[v] = GIP_KIND_CO;
        else if ( Aig_ObjIsCi(pObj) )
            p->pKind[v] = Saig_ObjIsPi( p->pAig, pObj ) ? GIP_KIND_PI : GIP_KIND_LO;
        else if ( Aig_ObjIsNode(pObj) && pCnf->pObj2Count[v] > 0 )
            p->pKind[v] = GIP_KIND_NODE;
        else
            p->pKind[v] = GIP_KIND_OTHER;
        p->pLoIdx[v] = p->pKind[v] == GIP_KIND_LO ? p->nLo++ : -1;
        // leaves (the clauses of a node refer only to variables with smaller ids: its cut leaves)
        for ( m = 0; m < 2; m++ )
            for ( b = 0; b < 2; b++ )
                p->pCc[4*v + 2*m + b] = p->pKind[v] == GIP_KIND_PI ? (m ? 1 : 0) : (p->pKind[v] == GIP_KIND_LO ? 1 : 0);
        if ( p->pKind[v] != GIP_KIND_NODE && p->pKind[v] != GIP_KIND_CO )
            continue;
        for ( m = 0; m < 2; m++ )
            for ( b = 0; b < 2; b++ )
            {
                int LitV = Gip_Lit( v, 1 ^ b ), Best = GIP_CC_MAX;
                for ( c = pCnf->pObj2Clause[v]; c < pCnf->pObj2Clause[v] + pCnf->pObj2Count[v]; c++ )
                {
                    int * pLit, fHas = 0, Sum = m;
                    for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
                    {
                        if ( *pLit == LitV )
                            fHas = 1;
                        else if ( Gip_LitVar(*pLit) != v )
                        {
                            assert( Gip_LitVar(*pLit) < v );
                            Sum += Gip_CcLitTrue( p->pCc, Gip_LitNot(*pLit), m );   // the other literals must be false
                            if ( Sum > GIP_CC_MAX )
                                Sum = GIP_CC_MAX;
                        }
                    }
                    if ( fHas && Sum < Best )
                        Best = Sum;
                }
                p->pCc[4*v + 2*m + b] = Best;
            }
    }
    p->pLoIdx[p->nVars] = -1;
    // the defining clauses of a node by the sign of the node's own literal. A node with a value can only be
    // open in a clause that contains its false literal; when the clauses with one sign all come before those with the other, that
    // group is a range and the others need not be visited. A node whose clauses are not grouped like that (or with a clause that
    // does not contain it) keeps the full scan.
    p->pClsSplit = ABC_ALLOC( int, p->nVars + 1 );
    p->pClsPol0  = ABC_CALLOC( char, p->nVars + 1 );
    for ( v = 0; v < p->nVars + 1; v++ )
        p->pClsSplit[v] = -1;
    for ( v = 0; v < p->nVars; v++ )
    {
        int c0 = pCnf->pObj2Clause[v], c1 = c0 + pCnf->pObj2Count[v], Split = -1, Pol0 = -1, fOk = pCnf->pObj2Count[v] > 0;
        for ( c = c0; c < c1 && fOk; c++ )
        {
            int * pLit, Pol = -1;
            for ( pLit = pCnf->pClauses[c]; pLit < pCnf->pClauses[c+1]; pLit++ )
                if ( Gip_LitVar(*pLit) == v )
                {
                    if ( Pol != -1 )
                        fOk = 0;   // the var twice in one clause
                    Pol = Gip_LitCompl( *pLit );
                }
            if ( Pol == -1 )
                fOk = 0;
            else if ( Pol0 == -1 )
                Pol0 = Pol;
            else if ( Pol != Pol0 && Split == -1 )
                Split = c;
            else if ( Pol == Pol0 && Split != -1 )
                fOk = 0;   // the first sign again after the second: not grouped
        }
        if ( !fOk )
            continue;
        p->pClsSplit[v] = Split == -1 ? c1 : Split;
        p->pClsPol0[v]  = (char)Pol0;
    }
}

// ---- the incremental lemma cover: dirty bits, and per register literal the clean positions it is the witness of
// the index of the lowest set bit of a word that is not zero
static inline int Gip_WordFirstBit( word w )
{
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_ctzll( w );
#else
    int n = 0;
    if ( (w & ABC_CONST(0x00000000FFFFFFFF)) == 0 ) { n += 32; w >>= 32; }
    if ( (w & ABC_CONST(0x000000000000FFFF)) == 0 ) { n += 16; w >>= 16; }
    if ( (w & ABC_CONST(0x00000000000000FF)) == 0 ) { n +=  8; w >>=  8; }
    if ( (w & ABC_CONST(0x000000000000000F)) == 0 ) { n +=  4; w >>=  4; }
    if ( (w & ABC_CONST(0x0000000000000003)) == 0 ) { n +=  2; w >>=  2; }
    if ( (w & ABC_CONST(0x0000000000000001)) == 0 ) { n++; }
    return n;
#endif
}
// the first dirty position in [From, To), or -1
static int Gip_IncNextDirty( Gip_Solver_t * p, int From, int To )
{
    int iW, nW = (To + 63) >> 6;
    word w;
    if ( From >= To )
        return -1;
    iW = From >> 6;
    w = p->Jftr.pIncDirty[iW] & (~(word)0 << (From & 63));
    while ( w == 0 )
    {
        // the next word that is not zero, from the summary
        int iS;
        word s;
        if ( ++iW >= nW )
            return -1;
        iS = iW >> 6;
        s = p->Jftr.pIncSum[iS] & (~(word)0 << (iW & 63));
        while ( s == 0 )
        {
            if ( ++iS > ((nW - 1) >> 6) )
                return -1;
            s = p->Jftr.pIncSum[iS];
        }
        iW = (iS << 6) + Gip_WordFirstBit( s );
        if ( iW >= nW )
            return -1;
        w = p->Jftr.pIncDirty[iW];
    }
    iW = (iW << 6) + Gip_WordFirstBit( w );
    return iW < To ? iW : -1;
}
// room for the positions below nPos (new words are zero)
static void Gip_IncReserve( Gip_Solver_t * p, int nPos )
{
    int nW = (nPos + 63) >> 6, nOld = p->Jftr.nIncWords;
    if ( nW <= nOld )
        return;
    nW = Abc_MaxInt( nW, 2 * nOld );
    p->Jftr.pIncDirty = ABC_REALLOC( word, p->Jftr.pIncDirty, nW );
    memset( p->Jftr.pIncDirty + nOld, 0, sizeof(word) * (nW - nOld) );
    p->Jftr.pIncSum = ABC_REALLOC( word, p->Jftr.pIncSum, (nW + 63) >> 6 );
    memset( p->Jftr.pIncSum + ((nOld + 63) >> 6), 0, sizeof(word) * (((nW + 63) >> 6) - ((nOld + 63) >> 6)) );
    p->Jftr.nIncWords = nW;
}
// the positions whose witness is this literal become dirty (the literal is false now, or false in pM); they leave its list
static void Gip_IncDirtyLit( Gip_Solver_t * p, int Lit )
{
    Vec_Int_t * vList = p->Jftr.pIncOcc[2 * p->pCtx->pLoIdx[Gip_LitVar(Lit)] + Gip_LitCompl(Lit)];
    int i, pos;
    if ( vList == NULL || Vec_IntSize(vList) == 0 )
        return;
    Vec_IntForEachEntry( vList, pos, i )
        if ( p->Jftr.pIncListed[pos] == Lit )
        {
            Gip_IncSetDirty( p, pos );
            p->Jftr.pIncListed[pos] = -1;
        }
    Vec_IntClear( vList );
}

// records the lemma clause at this position of Cdb.vLemmas (its literals are register literals)
static void Gip_JftrOccAdd( Gip_Solver_t * p, int pos )
{
    Gip_Ctx_t * pCtx = p->pCtx;
    int Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
    int * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    int i, Var, fSat0 = 0;
    if ( pos >= p->Jftr.nCntAlloc )
    {
        int nNew = Abc_MaxInt( 2 * p->Jftr.nCntAlloc, pos + 1024 );
        p->Jftr.pWit  = ABC_REALLOC( int,  p->Jftr.pWit,  nNew );
        p->Jftr.pSat0 = ABC_REALLOC( char, p->Jftr.pSat0, nNew );
        p->Jftr.pIncListed = ABC_REALLOC( int, p->Jftr.pIncListed, nNew );
        Gip_IncReserve( p, nNew );
        p->Jftr.nCntAlloc = nNew;
    }
    for ( i = 0; i < nLits; i++ )
    {
        Var = Gip_LitVar( pLits[i] );
        if ( pCtx->pKind[Var] != GIP_KIND_LO )
        {
            // lemma clauses are over register outputs; anything else is not counted and the
            // clause is treated as never satisfied by it: a decision on it is still allowed
            continue;
        }
        if ( Gip_SolverLitValue(p, pLits[i]) == GIP_TRUE && p->pLevel[Var] == 0 )
            fSat0 = 1;
    }
    p->Jftr.pWit[pos]  = -1;
    p->Jftr.pSat0[pos] = (char)fSat0;
    p->Jftr.pIncListed[pos] = -1;
    Gip_IncSetDirty( p, pos );   // a new position is examined before it is passed
}

// rebuilds the clause side from the current lemma list (at level 0, between solves)
void Gip_SolverJftrRebuild( Gip_Solver_t * p )
{
    int i, pos;
    assert( Gip_SolverLevelOf(p) == 0 );
    p->Jftr.fBuilt = 1;
    if ( p->Jftr.pIncOcc == NULL )
        p->Jftr.pIncOcc = ABC_CALLOC( Vec_Int_t *, 2 * Abc_MaxInt(p->pCtx->nLo, 1) );
    else
        for ( i = 0; i < 2 * p->pCtx->nLo; i++ )
            if ( p->Jftr.pIncOcc[i] )
                Vec_IntClear( p->Jftr.pIncOcc[i] );
    Vec_IntClear( p->Jftr.vIncVol );
    if ( p->Jftr.nIncWords )
    {
        memset( p->Jftr.pIncDirty, 0, sizeof(word) * p->Jftr.nIncWords );
        memset( p->Jftr.pIncSum, 0, sizeof(word) * ((p->Jftr.nIncWords + 63) >> 6) );
    }
    p->Jftr.nIncSeen = Vec_IntSize( p->vTrail );   // every position is dirty after the rebuild: the root facts before here need no look
    for ( pos = 0; pos < Vec_IntSize(p->Cdb.vLemmas); pos++ )
        Gip_JftrOccAdd( p, pos );
    p->Jftr.fOccDirty = 0;
}

// a lemma clause was appended to the list (only while the clause side exists and is clean)
void Gip_SolverJftrLemmaAdded( Gip_Solver_t * p )
{
    if ( !p->Jftr.fBuilt || p->Jftr.fOccDirty )
        return;
    Gip_JftrOccAdd( p, Vec_IntSize(p->Cdb.vLemmas) - 1 );
}

/**Function*************************************************************

  Synopsis    [Creates the jftr state of a solver, starts the mode for one solve, frees the state.]

  Description [Gip_SolverJftrInit gives the solver fresh state. It is used
  for a new solver and for a copy made by *p = *pSrc, whose pointers still
  belong to the source: they are dropped here, not freed. The level of the
  debug checks is kept. Gip_SolverJftrStart is called by a solve that has
  a budget, after the round is set up and before the search.]

***********************************************************************/
void Gip_SolverJftrInit( Gip_Solver_t * p )
{
    int fVerify = p->Jftr.fVerify;
    memset( &p->Jftr, 0, sizeof(Gip_Jftr_t) );
    p->Jftr.fVerify    = fVerify;
    p->Jftr.vAssumpOwn = Vec_IntAlloc( 16 );
    p->Jftr.vFront     = Vec_IntAlloc( 100 );
    p->Jftr.vMarked    = Vec_IntAlloc( 100 );
    p->Jftr.vRootOpen  = Vec_IntAlloc( 16 );
    p->Jftr.vRootFront = Vec_IntAlloc( 16 );
    p->Jftr.vCst       = Vec_IntAlloc( 4 );
    p->Jftr.vCstWit    = Vec_IntAlloc( 4 );
    p->Jftr.vCstFree   = Vec_IntAlloc( 4 );
    p->Jftr.vIncVol    = Vec_IntAlloc( 64 );
}
void Gip_SolverJftrStart( Gip_Solver_t * p, int * pAssump, int nAssump )
{
    int i;
    p->Jftr.fActive = 1;
    p->Jftr.nAssumpCur = nAssump;
    if ( p->pCtx->pKind == NULL )
        Gip_CtxPrepareJftr( p->pCtx );
    if ( !p->Jftr.fBuilt || p->Jftr.fOccDirty )
        Gip_SolverJftrRebuild( p );
    Gip_SolverJftrIncRoot( p );   // root facts since the last solve in the mode, e.g. units learnt by ordinary solves
    Vec_IntClear( p->Jftr.vFront );
    if ( p->Jftr.pCur == NULL )
        p->Jftr.pCur = ABC_ALLOC( int, p->nVarsAlloc );
    if ( p->Jftr.pM == NULL )
    {
        // the completion starts as the saved phases (no phase = false, as in the ordinary decision)
        p->Jftr.pM = ABC_ALLOC( char, Abc_MaxInt(p->pCtx->nLo, 1) );
        for ( i = 0; i < p->nVars; i++ )
            if ( p->pCtx->pLoIdx[i] >= 0 )
                p->Jftr.pM[p->pCtx->pLoIdx[i]] = p->pPhase[i] == GIP_TRUE ? GIP_TRUE : GIP_FALSE;
    }
    p->Jftr.iScan = p->Jftr.iCheck = Vec_IntSize( p->vTrail );
    p->Jftr.iLo = 0;
    p->Jftr.nVerified = p->Jftr.iVerStart = 0;
    // the solver keeps its own copy: the answer is read after the solve returned, when the caller's array may be gone
    Vec_IntClear( p->Jftr.vAssumpOwn );
    for ( i = 0; i < nAssump; i++ )
        Vec_IntPush( p->Jftr.vAssumpOwn, pAssump[i] );
    p->Jftr.pAssump = Vec_IntArray( p->Jftr.vAssumpOwn );
    p->Jftr.nAssump = nAssump;
    p->Jftr.fRootNewSolve = p->Jftr.fRootRecheck = 1;
    Vec_IntClear( p->Jftr.vCstFree );
}
void Gip_SolverJftrFree( Gip_Solver_t * p )
{
    int i;
    ABC_FREE( p->Jftr.pWit );
    ABC_FREE( p->Jftr.pSat0 );
    ABC_FREE( p->Jftr.pCur );
    ABC_FREE( p->Jftr.pM );
    if ( p->Jftr.pIncOcc )
        for ( i = 0; i < 2 * p->pCtx->nLo; i++ )
            Vec_IntFreeP( &p->Jftr.pIncOcc[i] );
    ABC_FREE( p->Jftr.pIncOcc );
    ABC_FREE( p->Jftr.pIncDirty );
    ABC_FREE( p->Jftr.pIncSum );
    ABC_FREE( p->Jftr.pIncListed );
    Vec_IntFreeP( &p->Jftr.vAssumpOwn );
    Vec_IntFreeP( &p->Jftr.vFront );
    Vec_IntFreeP( &p->Jftr.vMarked );
    Vec_IntFreeP( &p->Jftr.vRootOpen );
    Vec_IntFreeP( &p->Jftr.vRootFront );
    Vec_IntFreeP( &p->Jftr.vCst );
    Vec_IntFreeP( &p->Jftr.vCstWit );
    Vec_IntFreeP( &p->Jftr.vCstFree );
    Vec_IntFreeP( &p->Jftr.vIncVol );
}

// at the start of a jftr solve, at level 0: the root facts since the last look falsify the witnesses on their other literal
void Gip_SolverJftrIncRoot( Gip_Solver_t * p )
{
    int i, Lit;
    if ( p->Jftr.pIncOcc == NULL )
        return;
    if ( p->Jftr.nIncSeen > Vec_IntSize(p->vTrail) )
        p->Jftr.nIncSeen = 0;   // cannot happen: the root trail only grows, or loses activation literals with the index adjusted; look at all of it
    for ( i = p->Jftr.nIncSeen; i < Vec_IntSize(p->vTrail); i++ )
    {
        Lit = Vec_IntEntry( p->vTrail, i );
        if ( Gip_LitVar(Lit) < p->nVars && p->pCtx->pKind[Gip_LitVar(Lit)] == GIP_KIND_LO )
            Gip_IncDirtyLit( p, Gip_LitNot(Lit) );
    }
    p->Jftr.nIncSeen = Vec_IntSize( p->vTrail );
}

// the register literal holds in the completion of the current assignment: it is true, or unassigned and true in pM
static inline int Gip_JftrLitCovers( Gip_Solver_t * p, int Lit )
{
    int v = Gip_SolverLitValue(p, Lit);
    return v == GIP_TRUE || (v == GIP_NONE && p->Jftr.pM[p->pCtx->pLoIdx[Gip_LitVar(Lit)]] == (Gip_LitCompl(Lit) ? GIP_FALSE : GIP_TRUE));
}
// the position is covered (settled at level 0, or its witness covers it): it is clean, on the list of its witness
// once), and on the volatile list when the witness is true on the trail but not in pM (a backtrack can end its cover
static inline void Gip_IncClean( Gip_Solver_t * p, int pos )
{
    int Wit = p->Jftr.pWit[pos];
    Gip_IncClearDirty( p, pos );
    if ( p->Jftr.pSat0[pos] )
        return;
    if ( p->Jftr.pIncListed[pos] != Wit )
    {
        Vec_Int_t ** ppList = p->Jftr.pIncOcc + 2 * p->pCtx->pLoIdx[Gip_LitVar(Wit)] + Gip_LitCompl(Wit);
        if ( *ppList == NULL )
            *ppList = Vec_IntAlloc( 8 );
        else if ( Vec_IntSize(*ppList) >= 64 && (Vec_IntSize(*ppList) & (Vec_IntSize(*ppList) - 1)) == 0 )
        {
            // stale entries: positions whose witness changed since they were listed here; dropped at each doubling
            int i, k = 0, q;
            Vec_IntForEachEntry( *ppList, q, i )
                if ( p->Jftr.pIncListed[q] == Wit )
                    Vec_IntWriteEntry( *ppList, k++, q );
            Vec_IntShrink( *ppList, k );
        }
        Vec_IntPush( *ppList, pos );
        p->Jftr.pIncListed[pos] = Wit;
    }
    if ( p->Jftr.pM[p->pCtx->pLoIdx[Gip_LitVar(Wit)]] != (Gip_LitCompl(Wit) ? GIP_FALSE : GIP_TRUE) )
        Vec_IntPush( p->Jftr.vIncVol, pos );
}
// the verification of the lemma cover starts again: a literal that covered a clause may not hold any more
static inline void Gip_JftrCoverRestart( Gip_Solver_t * p )
{
    p->Jftr.nVerified = 0;  p->Jftr.iVerStart = p->Jftr.iLo;
}
// the value the plain search would give the literal's var: its saved phase, false when it has none (as Gip_SolverDecide)
static inline int Gip_JftrLitPreferred( Gip_Solver_t * p, int Lit )
{
    int Ph = p->pPhase[Gip_LitVar(Lit)];
    return Ph == GIP_NONE ? Gip_LitCompl(Lit) : Ph == (char)(1 ^ Gip_LitCompl(Lit));
}

// the literal of a lemma / constraint clause to make true: the last unassigned one that its var's preferred value makes true
// Gip_JftrLitPreferred), else the first unassigned one; -1 if none (the clause then has a true literal, or is falsified
static inline int Gip_JftrPickClauseLit( Gip_Solver_t * p, int * pLits, int nLits, int * pfTrue0, int * pfTrue )
{
    int i, Best = -1;
    *pfTrue0 = *pfTrue = 0;
    for ( i = 0; i < nLits; i++ )
    {
        int Lit = pLits[i], Var = Gip_LitVar( Lit ), v = Gip_SolverLitValue(p, Lit);
        if ( v == GIP_TRUE )
        {
            *pfTrue = 1;
            p->Jftr.iTrueLit = Lit;
            if ( p->pLevel[Var] == 0 )
                *pfTrue0 = 1;
            return -1;
        }
        if ( v != GIP_NONE )
            continue;
        if ( Best == -1 || Gip_JftrLitPreferred(p, Lit) )
            Best = Lit;
    }
    return Best;
}

// a defining clause of the assigned var that has no true literal, or -1 (clause index into the static CNF)
static inline int Gip_JftrOpenClause( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
    int c, c0 = pCnf->pObj2Clause[Var], c1 = c0 + pCnf->pObj2Count[Var];
    for ( c = c0; c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, fSat = 0;
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( *pLit == FalseLit )
                fHasFalse = 1;
            else if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE )
            {
                fSat = 1;
                break;
            }
        }
        if ( fHasFalse && !fSat )
            return c;
    }
    return -1;
}

// as Gip_JftrOpenClause for a var assigned above level 0, resumed at the var's cursor: the clauses before it
// were found satisfied after the scan last queued the var, and a satisfied clause stays satisfied until a literal is unassigned; every
// backtrack makes the scan queue again all the nodes assigned above level 0 (iCheck), which resets their cursors before any is popped
static inline int Gip_JftrOpenClauseNext( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
    int c, c1 = pCnf->pObj2Clause[Var] + pCnf->pObj2Count[Var];
    for ( c = p->Jftr.pCur[Var]; c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, fSat = 0;
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( *pLit == FalseLit )
                fHasFalse = 1;
            else if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE )
            {
                fSat = 1;
                break;
            }
        }
        if ( fHasFalse && !fSat )
            break;
    }
    p->Jftr.pCur[Var] = c;
    return c < c1 ? c : -1;
}
// the clauses of Var that contain its false literal, as a range [*pc0, *pc1); 0 when the var's clauses are not grouped by sign
static inline int Gip_JftrFalseRange( Gip_Solver_t * p, int Var, int * pc0, int * pc1 )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int Split = p->pCtx->pClsSplit[Var];
    if ( Split < 0 )
        return 0;
    // the false literal is negative when the value is true
    if ( (p->pValue[Var] == GIP_TRUE) == (int)p->pCtx->pClsPol0[Var] )
        *pc0 = pCnf->pObj2Clause[Var], *pc1 = Split;
    else
        *pc0 = Split, *pc1 = pCnf->pObj2Clause[Var] + pCnf->pObj2Count[Var];
    return 1;
}
// as Gip_JftrOpenClauseNext over the clauses that contain the var's false literal only: every other clause of
// the var contains its true literal and is never open, and in the clauses visited the var's own literal is false, so the test is "no
// literal is true". The cursor and the clause returned are those of Gip_JftrOpenClauseNext.
static inline int Gip_JftrOpenClauseRange( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int c, c0, c1;
    if ( !Gip_JftrFalseRange( p, Var, &c0, &c1 ) )
        return Gip_JftrOpenClauseNext( p, Var );
    for ( c = Abc_MaxInt( p->Jftr.pCur[Var], c0 ); c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1];
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE )
                break;
        }
        if ( pLit == pStop )
            break;
    }
    p->Jftr.pCur[Var] = c;
    if ( p->Jftr.fVerify )
    {
        // debug: against the full scan
        int cRef = Gip_JftrOpenClause( p, Var );
        if ( (c < c1 ? c : -1) != cRef )
            Gip_JftrFatal( p, "PDR2_JFTR_CHECK: the scan of the false-literal clauses and the full scan disagree" );
    }
    return c < c1 ? c : -1;
}
// the var was assigned by the propagation of one of its own defining clauses that still has every literal of
// its static clause: the clause contains the var's true literal (the var has the largest number in its defining clauses, the leaves of
// a cut have smaller ones) and all its other literals are false, so the assigned fanins force the value and no clause of the var is
// open, for as long as the var keeps this assignment (the fanins are before it on the trail). A stored clause that lost a literal
// at level 0 may be the clause of a fanout of the var; it does not count (GIP_CLA_WHOLE).
static inline int Gip_JftrOwnWhole( Gip_Solver_t * p, int Var )
{
    int Cref = p->pReason[Var], * pLits, nLits, k;
    if ( Cref == GIP_CREF_NONE || !Gip_ClaIsWholeTrans(&p->Cdb.Alloc, Cref) )
        return 0;
    pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );
    nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    for ( k = 0; k < nLits; k++ )
        if ( Gip_LitVar(pLits[k]) > Var )
            return 0;
    return 1;
}
// queues a var assigned above level 0 for examination from its first clause
static inline void Gip_JftrQueue( Gip_Solver_t * p, int Var )
{
    p->Jftr.pCur[Var] = p->pCtx->pCnf->pObj2Clause[Var];
    Vec_IntPush( p->Jftr.vFront, Var );
}

// the literal of the open clause to make true: the literal the var's preferred value makes true first (Gip_JftrLitPreferred: the
// early answer is then a restriction of the assignment the plain search prefers), then inputs (free, never in the cube), registers
// whose saved phase agrees, other registers, gates; then the lowest justification cost (registers needed, then gates), then the
// lowest activity
static inline int Gip_JftrPickLit( Gip_Solver_t * p, int c )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    char * pKind = p->pCtx->pKind;
    int * pLit, * pStop = pCnf->pClauses[c+1], Best = -1;
    int bestTier = 0, bestC0 = 0, bestC1 = 0;
    double bestAct = 0;
    for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
    {
        int Lit = *pLit, Var = Gip_LitVar( Lit ), tier, c0, c1;
        double act;
        if ( Gip_SolverLitValue(p, Lit) != GIP_NONE )
            continue;
        if ( pKind[Var] == GIP_KIND_PI )
            tier = 0;
        else if ( pKind[Var] == GIP_KIND_LO )
            tier = p->pPhase[Var] == (char)(1 ^ Gip_LitCompl(Lit)) ? 1 : 2;
        else
            tier = 3;
        tier = (Gip_JftrLitPreferred(p, Lit) ? 0 : 4) + tier;
        c0 = Gip_CcLitTrue( p->pCtx->pCc, Lit, 0 );
        c1 = Gip_CcLitTrue( p->pCtx->pCc, Lit, 1 );
        act = p->Vsids.Act.pAct[Var];
        if ( Best == -1 || tier < bestTier || (tier == bestTier && (c0 < bestC0 || (c0 == bestC0 && (c1 < bestC1 || (c1 == bestC1 && act < bestAct))))) )
        {
            Best = Lit; bestTier = tier; bestC0 = c0; bestC1 = c1; bestAct = act;
        }
    }
    if ( Best == -1 )
        Gip_JftrFatal( p, "an open defining clause has no unassigned literal (it is falsified)" );
    return Best;
}

// the justification walk from the assumptions: every node reached must be closed (each defining
// clause containing its false literal has a true literal); of the true literals of each such clause the
// first one of minimum cost is the justification, its var is marked and walked when it is a node or an output. Returns
// -1 when the walk closes, with the leaves (inputs, registers) marked; else the first open var
static int Gip_JftrWalk( Gip_Solver_t * p )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    char * pKind = p->pCtx->pKind;
    Vec_Int_t * vStack = p->Jftr.vFront;   // scratch: the frontier is empty when the walk runs
    int i, Var, Open = -1;
    assert( Vec_IntSize(vStack) == 0 );
    for ( i = 0; i < p->Jftr.nAssump; i++ )
    {
        Var = Gip_LitVar( p->Jftr.pAssump[i] );
        if ( Var >= p->nVars || p->pMark[Var] )
            continue;
        p->pMark[Var] = 1;
        Vec_IntPush( p->Jftr.vMarked, Var );
        if ( pKind[Var] == GIP_KIND_NODE || pKind[Var] == GIP_KIND_CO )
            Vec_IntPush( vStack, Var );
    }
    while ( Vec_IntSize(vStack) > 0 && Open == -1 )
    {
        int FalseLit, c, c0, c1;
        Var = Vec_IntPop( vStack );
        if ( p->pValue[Var] == GIP_NONE )
            continue;   // an unassigned node: not a justification source; only reached through an assumption
        FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
        c0 = pCnf->pObj2Clause[Var];
        c1 = c0 + pCnf->pObj2Count[Var];
        for ( c = c0; c < c1; c++ )
        {
            int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, Sat = -1, SatCost = 0;
            // Var is already marked. A clause starting with its true literal
            // either has no FalseLit (and was ignored), or is tautological:
            // the old minimum-cost witness is then already marked at cost 0.
            // Both cases add no leaf, so skip without changing any choices.
            // The static CNF writer puts the owner first, but correctness of
            // this conservative test does not depend on that layout.
            if ( pCnf->pClauses[c] < pStop && pCnf->pClauses[c][0] == Gip_LitNot(FalseLit) )
                continue;
            for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
            {
                int u = Gip_LitVar( *pLit ), Cost;
                if ( *pLit == FalseLit )
                {
                    fHasFalse = 1;
                    continue;
                }
                if ( Gip_SolverLitValue(p, *pLit) != GIP_TRUE )
                    continue;
                // the justification source: a var already in the walk, a level-0 fact or an input
                // costs nothing; otherwise a fixed cost by kind
                Cost = p->pMark[u] ? 0 : p->pLevel[u] == 0 ? 1 : pKind[u] == GIP_KIND_PI ? 2 : pKind[u] == GIP_KIND_LO ? 4 : 3;
                if ( Sat == -1 || Cost < SatCost )
                {
                    Sat = *pLit;
                    SatCost = Cost;
                }
            }
            if ( !fHasFalse )
                continue;
            if ( Sat == -1 )
            {
                Open = Var;
                break;
            }
            {
                int u = Gip_LitVar( Sat );
                if ( p->pMark[u] )
                    continue;
                p->pMark[u] = 1;
                Vec_IntPush( p->Jftr.vMarked, u );
                if ( pKind[u] == GIP_KIND_NODE || pKind[u] == GIP_KIND_CO )
                    Vec_IntPush( vStack, u );
            }
        }
    }
    Vec_IntClear( vStack );
    return Open;
}

// the early stop: the partial model keeps the assignments of level 0 and the leaves of the
// justification walk; the other inputs and registers assigned above level 0 are read as unassigned
// the trail keeps them: the next backtrack pops them like any other entry
static void Gip_JftrShrinkModel( Gip_Solver_t * p )
{
    char * pKind = p->pCtx->pKind;
    int i, Var;
    for ( i = Gip_SolverLevelOf(p) > 0 ? Vec_IntEntry(p->vPosInTrail, 0) : Vec_IntSize(p->vTrail); i < Vec_IntSize(p->vTrail); i++ )
    {
        Var = Gip_LitVar( Vec_IntEntry(p->vTrail, i) );
        if ( Var < p->nVars && (pKind[Var] == GIP_KIND_PI || pKind[Var] == GIP_KIND_LO) && !p->pMark[Var] )
            Gip_SolverSetNone( p, Var );
    }
    Vec_IntForEachEntry( p->Jftr.vMarked, Var, i )
        p->pMark[Var] = 0;
    Vec_IntClear( p->Jftr.vMarked );
}

// as Gip_JftrOpenClause, but only a literal true at level 0 closes a clause (the classification of a root node, valid in every solve)
static int Gip_JftrOpenClauseRoot( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
    int c, c0 = pCnf->pObj2Clause[Var], c1 = c0 + pCnf->pObj2Count[Var];
    for ( c = c0; c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, fSat = 0;
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( *pLit == FalseLit )
                fHasFalse = 1;
            else if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE && p->pLevel[Gip_LitVar(*pLit)] == 0 )
            {
                fSat = 1;
                break;
            }
        }
        if ( fHasFalse && !fSat )
            return c;
    }
    return -1;
}
// a defining clause of the root node that is open under the current assignment and active for the plain search: the propagation
// skips a clause that has an unassigned literal outside the domain, so only a clause whose unassigned literals are all in the domain
// constrains the answer. (The node itself may have left the domain: assigned vars are removed from it, their fanins stay.)
static int Gip_JftrOpenClauseDom( Gip_Solver_t * p, int Var )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    int FalseLit = Gip_Lit( Var, p->pValue[Var] == GIP_TRUE );
    int c, c0 = pCnf->pObj2Clause[Var], c1 = c0 + pCnf->pObj2Count[Var];
    for ( c = c0; c < c1; c++ )
    {
        int * pLit, * pStop = pCnf->pClauses[c+1], fHasFalse = 0, fSkip = 0;
        for ( pLit = pCnf->pClauses[c]; pLit < pStop; pLit++ )
        {
            if ( *pLit == FalseLit )
                fHasFalse = 1;
            else if ( Gip_SolverLitValue(p, *pLit) == GIP_TRUE || (Gip_SolverLitValue(p, *pLit) == GIP_NONE && !Gip_DomainHas(&p->Domain, Gip_LitVar(*pLit))) )
            {
                fSkip = 1;
                break;
            }
        }
        if ( fHasFalse && !fSkip )
            return c;
    }
    return -1;
}
// The nodes assigned at level 0 are facts of the formula (the asserted property and what it implies, learnt units). The plain search
// respects them by assigning every var of the domain; the early stop has to close them like the nodes assigned above level 0.
// vRootOpen keeps, across solves, the root nodes that no level-0 literal closes; vRootFront are those of this solve's domain.
static void Gip_JftrRootUpdate( Gip_Solver_t * p )
{
    int * pCount = p->pCtx->pCnf->pObj2Count;
    char * pKind = p->pCtx->pKind;
    int i, k, Var, iRootEnd = Gip_SolverLevelOf(p) > 0 ? Vec_IntEntry( p->vPosInTrail, 0 ) : Vec_IntSize( p->vTrail ), fGrew;
    if ( p->Jftr.nRootSeen > iRootEnd )
    {
        // not expected: the root trail only grows, except for the activation entries that Gip_SolverCleanTemporary removes and accounts for
        Vec_IntClear( p->Jftr.vRootOpen );
        p->Jftr.nRootSeen = 0;
    }
    if ( p->Jftr.nRootSeen == iRootEnd && !p->Jftr.fRootNewSolve )
        return;
    for ( i = p->Jftr.nRootSeen; i < iRootEnd; i++ )
    {
        Var = Gip_LitVar( Vec_IntEntry(p->vTrail, i) );
        if ( Var >= p->nVars || (pKind[Var] != GIP_KIND_NODE && pKind[Var] != GIP_KIND_CO) || pCount[Var] == 0 )
            continue;
        if ( Gip_JftrOpenClauseRoot( p, Var ) >= 0 )
            Vec_IntPush( p->Jftr.vRootOpen, Var );
    }
    fGrew = p->Jftr.nRootSeen < iRootEnd;
    p->Jftr.nRootSeen = iRootEnd;
    p->Jftr.fRootNewSolve = 0;
    Vec_IntClear( p->Jftr.vRootFront );
    k = 0;
    Vec_IntForEachEntry( p->Jftr.vRootOpen, Var, i )
    {
        // new root facts may have closed a kept node for good; without new facts the kept nodes are as they were
        if ( p->pValue[Var] == GIP_NONE || p->pLevel[Var] != 0 || (fGrew && Gip_JftrOpenClauseRoot( p, Var ) < 0) )
            continue;
        Vec_IntWriteEntry( p->Jftr.vRootOpen, k++, Var );
        Vec_IntPush( p->Jftr.vRootFront, Var );   // whether a clause of it is active in this domain is decided when it is examined
    }
    Vec_IntShrink( p->Jftr.vRootOpen, k );
}
// scans the trail from position iFrom for assigned vars with an open clause and pushes them
static inline void Gip_JftrScan( Gip_Solver_t * p )
{
    int * pCount = p->pCtx->pCnf->pObj2Count;
    char * pKind = p->pCtx->pKind;
    int i, Lit, Var, iFrom = Abc_MinInt( p->Jftr.iScan, p->Jftr.iCheck );
    if ( p->Jftr.fRootRecheck )
    {
        // the root nodes of the domain that are open under the current assignment go to the frontier (at the start of the solve and
        // after every backtrack, as the nodes above level 0 are rescanned)
        Gip_JftrRootUpdate( p );
        Vec_IntForEachEntry( p->Jftr.vRootFront, Var, i )
            if ( Gip_JftrOpenClauseDom( p, Var ) >= 0 )
                Vec_IntPush( p->Jftr.vFront, Var );
        p->Jftr.fRootRecheck = 0;
    }
    for ( i = iFrom; i < Vec_IntSize(p->vTrail); i++ )
    {
        Lit = Vec_IntEntry( p->vTrail, i );
        Var = Gip_LitVar( Lit );
        if ( Var >= p->nVars )
            continue;
        if ( pKind[Var] == GIP_KIND_LO )
        {
            if ( i >= p->Jftr.iScan && p->Jftr.pM[p->pCtx->pLoIdx[Var]] != p->pValue[Var] && p->Jftr.nVerified > 0 )
                Gip_JftrCoverRestart( p );   // a clause verified by the other literal of this register is not covered by it any more
            if ( i >= p->Jftr.iScan )
                Gip_IncDirtyLit( p, Gip_LitNot(Lit) );   // the witnesses on the literal this assignment falsifies
        }
        else if ( i >= p->Jftr.iCheck && pCount[Var] > 0 && p->pLevel[Var] > 0 )   // a node assigned at level 0 after a backtrack is a root node: Gip_JftrRootUpdate has it, with the clause test that respects the domain
        {
            if ( Gip_JftrOwnWhole(p, Var) )
            {
                // closed by its own fanins for as long as it is assigned: it would be popped, found closed and dropped
                if ( p->Jftr.fVerify )
                {
                    // debug: the node is closed
                    int cRef = Gip_JftrOpenClause( p, Var );
                    if ( cRef >= 0 )
                        Gip_JftrFatal( p, "PDR2_JFTR_CHECK: a node forced by its own whole defining clause has an open clause" );
                }
            }
            else
                Gip_JftrQueue( p, Var );   // examined once, when popped; the pops meet the open nodes in the same order
        }
    }
    p->Jftr.iScan = p->Jftr.iCheck = Vec_IntSize( p->vTrail );
}

// the registers the early answer assigned above level 0 take their values in the completion (before a shrink
// unassigns the ones the predecessor cube does not need): the answer is then "the assignment, else pM" for every register
static void Gip_JftrCoverCommit( Gip_Solver_t * p )
{
    int i;
    if ( Gip_SolverLevelOf(p) == 0 )
        return;
    for ( i = Vec_IntEntry(p->vPosInTrail, 0); i < Vec_IntSize(p->vTrail); i++ )
    {
        int Lit = Vec_IntEntry( p->vTrail, i ), Var = Gip_LitVar( Lit );
        if ( Var < p->nVars && p->pCtx->pKind[Var] == GIP_KIND_LO )
            p->Jftr.pM[p->pCtx->pLoIdx[Var]] = p->pValue[Var];
    }
    // no clean position of the incremental cover is volatile now: a witness that is true above level 0 is true in pM as well,
    // and one that is true at level 0 stays true; the next backtrack has nothing to make dirty
    Vec_IntClear( p->Jftr.vIncVol );
}
// the lemma clause at this position has a covering register literal (literals of other kinds do not count, a literal true at
// level 0 settles the clause for good)
static inline int Gip_JftrLemmaCovered( Gip_Solver_t * p, int pos )
{
    int Wit, Cref, * pLits, nLits, k;
    if ( p->Jftr.pSat0[pos] )
        return 1;
    Wit = p->Jftr.pWit[pos];
    if ( Wit >= 0 && Gip_JftrLitCovers(p, Wit) )
    {
        if ( p->Jftr.fVerify >= 2 )
        {
            // debug: the cached witness is a literal of the clause
            Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
            pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );  nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
            for ( k = 0; k < nLits; k++ )
                if ( pLits[k] == Wit )
                    break;
            if ( k == nLits )
                Gip_JftrFatal( p, "PDR2_JFTR_CHECK=2: the witness literal of a lemma clause is not in the clause" );
        }
        return 1;
    }
    Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
    pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );  nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
    for ( k = 0; k < nLits; k++ )
    {
        int Var = Gip_LitVar( pLits[k] );
        if ( p->pCtx->pKind[Var] != GIP_KIND_LO || !Gip_JftrLitCovers(p, pLits[k]) )
            continue;
        // a literal true at level 0 is not a witness: the caller finds it, moves the cursor and marks the clause as settled -- a root
        // fact that came after the last rebuild
        if ( Gip_SolverLitValue(p, pLits[k]) == GIP_TRUE && p->pLevel[Var] == 0 )
            continue;
        p->Jftr.pWit[pos] = pLits[k];
        return 1;
    }
    return 0;
}

// debug, PDR2_JFTR_CHECK=2) the reference of the incremental cover step: every clean position is covered
// by its witness, and the full scan from the same cursor, without writing anything, stops at the returned position (-1: none
static int Gip_IncReference( Gip_Solver_t * p, int n )
{
    int k, j, pos, Wit, Cref, * pLits, nLits;
    for ( pos = 0; pos < n; pos++ )
    {
        if ( Gip_IncIsDirty(p, pos) || p->Jftr.pSat0[pos] )
            continue;
        if ( p->Jftr.pWit[pos] < 0 || !Gip_JftrLitCovers(p, p->Jftr.pWit[pos]) )
            Gip_JftrFatal( p, "PDR2_JFTR_CHECK=2: the incremental cover has a clean lemma position that its witness does not cover" );
        Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
        pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );  nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
        for ( j = 0; j < nLits; j++ )
            if ( pLits[j] == p->Jftr.pWit[pos] )
                break;
        if ( j == nLits )
            Gip_JftrFatal( p, "PDR2_JFTR_CHECK=2: the witness of a clean lemma position is not a literal of its clause" );
    }
    for ( k = p->Jftr.nVerified; k < n; k++ )
    {
        pos = (p->Jftr.iVerStart + k) % n;
        Wit = p->Jftr.pWit[pos];
        if ( p->Jftr.pSat0[pos] || (Wit >= 0 && Gip_JftrLitCovers(p, Wit)) )
            continue;
        Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
        pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref );  nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
        for ( j = 0; j < nLits; j++ )   // as Gip_JftrLemmaCovered: a covering register literal that is not true at level 0
            if ( p->pCtx->pKind[Gip_LitVar(pLits[j])] == GIP_KIND_LO && Gip_JftrLitCovers(p, pLits[j]) &&
                 !(Gip_SolverLitValue(p, pLits[j]) == GIP_TRUE && p->pLevel[Gip_LitVar(pLits[j])] == 0) )
                break;
        if ( j == nLits )
            return pos;
    }
    return -1;
}

// debug, PDR2_JFTR_CHECK=2) every lemma clause really has a covering register literal (called where the cover is declared complete
static void Gip_JftrCoverVerify( Gip_Solver_t * p )
{
    int pos, k;
    for ( pos = 0; pos < Vec_IntSize(p->Cdb.vLemmas); pos++ )
    {
        int Cref = Vec_IntEntry( p->Cdb.vLemmas, pos ), * pLits = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nLits = Gip_ClaLen( &p->Cdb.Alloc, Cref );
        for ( k = 0; k < nLits; k++ )
            if ( p->pCtx->pKind[Gip_LitVar(pLits[k])] == GIP_KIND_LO && Gip_JftrLitCovers(p, pLits[k]) )
                break;
        if ( k == nLits )
            Gip_JftrFatal( p, "PDR2_JFTR_CHECK=2: a lemma clause has no covering register literal where the lemma cover was declared complete" );
    }
    p->Jftr.Ver.nCover += Vec_IntSize(p->Cdb.vLemmas);
}

// step 3 of the jftr decision: a constraint clause of the round without a true literal gets one (1 = a decision was made,
// 0 = every constraint clause has a true literal, -1 = a clause is falsified or no decision is possible: fall back)
static int Gip_JftrDecideCst( Gip_Solver_t * p )
{
    int i, Lit;
    for ( i = 0; i < Vec_IntSize(p->Jftr.vCst); i++ )
    {
        int Cref = Vec_IntEntry( p->Jftr.vCst, i ), fTrue0, fTrue, Wit = Vec_IntEntry( p->Jftr.vCstWit, i );
        if ( Wit >= 0 && Gip_SolverLitValue(p, Wit) == GIP_TRUE )
            continue;
        if ( Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
            continue;
        {
            // A constraint clause with an unassigned literal outside the domain is not enforced by the propagation (that var is a
            // free register outside the cone of the query: the nested generalization of a CTG lemma fixes the domain to its own
            // cube, while the clause "not full" of the parent is over the parent's registers). The mode leaves such a clause alone
            // too: a decision must not assign a var outside the domain.
            // The free var must be a register (a leaf, which a completion can set), and the clauses left alone in one solve must
            // not need opposite values of the same register: vCstFree keeps one free literal per such clause.
            int * pL = Gip_ClaLits( &p->Cdb.Alloc, Cref ), nL = Gip_ClaLen( &p->Cdb.Alloc, Cref ), k, fFree = 0, Pick = -1;
            for ( k = 0; k < nL; k++ )
                if ( Gip_SolverLitValue(p, pL[k]) == GIP_TRUE )
                    break;
            for ( k = k < nL ? nL : 0; k < nL; k++ )   // a clause with a true literal takes the ordinary path below
            {
                if ( Gip_SolverLitValue(p, pL[k]) != GIP_NONE || Gip_DomainHas( &p->Domain, Gip_LitVar(pL[k]) ) )
                    continue;
                fFree = 1;
                if ( Gip_LitVar(pL[k]) >= p->nVars || p->pCtx->pKind[Gip_LitVar(pL[k])] != GIP_KIND_LO )
                    Gip_JftrFatal( p, "a constraint clause has an unassigned literal outside the domain that is not a register" );
                if ( Vec_IntFind( p->Jftr.vCstFree, pL[k] ) >= 0 )
                {
                    Pick = -2;   // already recorded for this or another clause
                    break;
                }
                if ( Pick == -1 && Vec_IntFind( p->Jftr.vCstFree, Gip_LitNot(pL[k]) ) < 0 )
                    Pick = pL[k];
            }
            if ( fFree )
            {
                // a conservative test: one literal per clause is recorded in the order met, so a satisfiable pair can be rejected;
                // in the PDR engine only the single clause "not full" of a parent cube is left alone
                if ( Pick == -1 )
                    Gip_JftrFatal( p, "the constraint clauses left to free registers outside the domain have no compatible literals recorded" );
                if ( Pick >= 0 )
                {
                    Vec_IntPush( p->Jftr.vCstFree, Pick );
                    // the recorded polarity is the register's value in the completion of this answer
                    Gip_IncDirtyLit( p, Gip_LitNot(Pick) );   // the witnesses on the literal that is false in the completion now
                    p->Jftr.pM[p->pCtx->pLoIdx[Gip_LitVar(Pick)]] = Gip_LitCompl(Pick) ? GIP_FALSE : GIP_TRUE;
                    Gip_JftrCoverRestart( p );
                }
                continue;
            }
        }
        Lit = Gip_JftrPickClauseLit( p, Gip_ClaLits(&p->Cdb.Alloc, Cref), Gip_ClaLen(&p->Cdb.Alloc, Cref), &fTrue0, &fTrue );
        if ( Lit == -1 )
        {
            if ( fTrue )
            {
                Vec_IntWriteEntry( p->Jftr.vCstWit, i, p->Jftr.iTrueLit );
                continue;
            }
            return -1;   // falsified: propagation would have reported it
        }
        Vec_IntWriteEntry( p->Jftr.vCstWit, i, Lit );
        Gip_SolverNewLevel( p );
        Gip_JftrNoteDecision( p, Lit, 1 );
        Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
        p->Stats.nDecisions++;
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [The jftr decision: makes true a literal of an open or uncovered clause.]

  Description [Returns 1 after a decision, 0 when the partial assignment
  is an early answer (see JFTR MODE above): no assigned node has an open
  clause, every lemma clause is covered and every constraint clause of the
  round is satisfied or left to a free register. Registers and outputs
  that nothing requires stay unassigned.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverDecideJftr( Gip_Solver_t * p )
{
    char * pKind = p->pCtx->pKind;
    int i, Var, Lit, c, nPass = 0;
    while ( 1 )
    {
        // 1. the assignments since the last scan may have opened clauses
        Gip_JftrScan( p );
        // 2. the constraint clauses of this round (few, checked directly), before the gates
        {
            int r = Gip_JftrDecideCst( p );
            if ( r < 0 )
                Gip_JftrFatal( p, "a constraint clause of the round has neither a true nor an unassigned literal" );
            if ( r > 0 )
            {
                return 1;
            }
        }
        // 3. an open clause: make one of its literals true
        while ( Vec_IntSize(p->Jftr.vFront) > 0 )
        {
            Var = Vec_IntPop( p->Jftr.vFront );
            if ( p->pValue[Var] == GIP_NONE || (c = (p->pLevel[Var] == 0 ? Gip_JftrOpenClauseDom(p, Var) : Gip_JftrOpenClauseRange(p, Var))) < 0 )
                continue;
            Lit = Gip_JftrPickLit( p, c );
            // the node stays on the frontier: the decision closes this clause, another defining clause of the node may still be open
            // a node whose function has several cubes needs one true literal in each clause that contains its false literal
            Vec_IntPush( p->Jftr.vFront, Var );
            Gip_SolverNewLevel( p );
            Gip_JftrNoteDecision( p, Lit, 0 );
            Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
            p->Stats.nDecisions++;
            return 1;
        }
        // 4. the lemma clauses: one without a covering witness
        if ( p->Jftr.fVerify >= 2 && p->Jftr.nVerified >= Vec_IntSize(p->Cdb.vLemmas) )
            Gip_IncReference( p, Vec_IntSize(p->Cdb.vLemmas) );   // debug: the clean positions are covered also when the step is skipped
        while ( p->Jftr.nVerified < Vec_IntSize(p->Cdb.vLemmas) )
        {
            int n = Vec_IntSize( p->Cdb.vLemmas ), pos = -1, Cref, fTrue0, fTrue, iRef = -2;
            // The positions are visited cyclically from the cursor; a run of n covered positions without an unassignment in between
            // means that every lemma clause is covered. A full scan would pass a clean position without any change (its witness
            // covers it), so only the dirty positions are examined, in the same cyclic order from the same cursor: the same position
            // is picked, the same witnesses are written (checked against the full scan under PDR2_JFTR_CHECK=2)
            if ( p->Jftr.fVerify >= 2 )
                iRef = Gip_IncReference( p, n );
            while ( p->Jftr.nVerified < n )
            {
                int q0 = (p->Jftr.iVerStart + p->Jftr.nVerified) % n, d = Gip_IncNextDirty( p, q0, n ), nSkip;
                if ( d >= 0 )
                    nSkip = d - q0;
                else
                {
                    d = Gip_IncNextDirty( p, 0, q0 );
                    nSkip = d >= 0 ? d + n - q0 : n;
                }
                if ( p->Jftr.nVerified + nSkip >= n )
                {
                    p->Jftr.nVerified = n;
                    break;
                }
                p->Jftr.nVerified += nSkip;
                if ( !Gip_JftrLemmaCovered( p, d ) )
                {
                    pos = d;
                    break;
                }
                Gip_IncClean( p, d );
                p->Jftr.nVerified++;
            }
            if ( iRef != -2 && iRef != pos )
                Gip_JftrFatal( p, "PDR2_JFTR_CHECK=2: the incremental cover picked another lemma position than the full scan" );
            if ( pos == -1 )
            {
                if ( p->Jftr.fVerify >= 2 )
                    Gip_JftrCoverVerify( p );
                break;
            }
            p->Jftr.iLo = pos + 1;
            Cref = Vec_IntEntry( p->Cdb.vLemmas, pos );
            Lit = Gip_JftrPickClauseLit( p, Gip_ClaLits(&p->Cdb.Alloc, Cref), Gip_ClaLen(&p->Cdb.Alloc, Cref), &fTrue0, &fTrue );
            if ( Lit == -1 )
            {
                if ( fTrue0 )
                {
                    // satisfied for good by a fact learnt since the rebuild
                    p->Jftr.pSat0[pos] = 1;
                    Gip_IncClean( p, pos );
                    p->Jftr.nVerified++;
                    continue;
                }
                Gip_JftrFatal( p, "a lemma clause is uncovered but has no unassigned literal (falsified, or a true literal that the cover missed)" );
            }
            if ( pKind[Gip_LitVar(Lit)] == GIP_KIND_LO )
            {
                p->Jftr.pWit[pos] = Lit;   // the decision makes this literal true
                p->Jftr.nVerified++;
            }
            else
                p->Jftr.nVerified = 0, p->Jftr.iVerStart = p->Jftr.iLo;   // a literal that is not a register is no witness: the clause is met again
            Gip_SolverNewLevel( p );
            Gip_JftrNoteDecision( p, Lit, 2 );
            Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
            if ( pKind[Gip_LitVar(Lit)] == GIP_KIND_LO )
                Gip_IncClean( p, pos );   // after the assignment: its witness, the decided literal, covers it now
            p->Stats.nDecisions++;
            return 1;
        }
        // 5. nothing left on the fast paths. A yes/no query stops here: every node assigned above
        // level 0 is closed (rechecked after backtracks) and the clause side holds. A query whose
        // model becomes a predecessor cube also needs the leaves under the transition relation alone:
        // the justification walk from the assumptions covers the level-0 node facts (which may come
        // from lemmas or the property) and marks the leaves; an open var goes back to the frontier
        if ( !p->Jftr.fLeaves )
        {
            if ( p->Jftr.fVerify )
                Gip_JftrVerifyEarly( p );
            if ( p->Jftr.fVerify >= 2 )
                Gip_JftrVerifyModel( p );
            Gip_JftrCoverCommit( p );
            return 0;
        }
        Var = Gip_JftrWalk( p );
        if ( Var == -1 )
        {
            p->Jftr.fWalkClosed = 1;
            if ( p->Jftr.fVerify )
                Gip_JftrVerifyEarly( p );   // before the shrink: the shrunk answer keeps the leaves only
            if ( p->Jftr.fVerify >= 2 )
                Gip_JftrVerifyModel( p );
            Gip_JftrCoverCommit( p );
            if ( p->Jftr.fShrink )
                Gip_JftrShrinkModel( p );
            else
            {
                Vec_IntForEachEntry( p->Jftr.vMarked, i, c )
                    p->pMark[i] = 0;
                Vec_IntClear( p->Jftr.vMarked );
            }
            return 0;
        }
        Vec_IntForEachEntry( p->Jftr.vMarked, i, c )
            p->pMark[i] = 0;
        Vec_IntClear( p->Jftr.vMarked );
        Gip_JftrQueue( p, Var );
        if ( nPass++ > 1000 )
            Gip_JftrFatal( p, "the justification walk keeps finding open nodes" );
    }
}

// Debug (PDR2_JFTR_CHECK >= 2): the state that flip-to-none leaves. Flip-to-none releases the value of a register of a full model
// when every clause it watches keeps another true literal (or an unassigned literal outside the domain, which the propagation
// restricted to the domain treats the same way); it reads the watch lists only. This check does not: every defining clause of
// every node (a node removed from the domain at level 0 still constrains its fanins), every lemma, constraint and learnt clause
// must have a true literal or an unassigned literal outside the domain. It tests that the releases preserved this clause condition
// of the domain-restricted search; it is not by itself a proof that one completion satisfies all clauses (the checks of the answer
// and of its completion, Gip_JftrVerifyModel, are separate and stay).
static int Gip_VerClauseFlipped( Gip_Solver_t * p, int * pLits, int nLits )
{
    int k;
    for ( k = 0; k < nLits; k++ )
        if ( Gip_SolverLitValue(p, pLits[k]) == GIP_TRUE || (Gip_SolverLitValue(p, pLits[k]) == GIP_NONE && !Gip_DomainHas(&p->Domain, Gip_LitVar(pLits[k]))) )
            return 1;
    return 0;
}
void Gip_JftrVerifyFlipped( Gip_Solver_t * p )
{
    Cnf_Dat_t * pCnf = p->pCtx->pCnf;
    char * pKind;
    Vec_Int_t * vLists[3] = { p->Cdb.vLemmas, p->Cdb.vTemp, p->Cdb.vLearnt };   // vTemp: the round's constraint clauses and the temporary learnt clauses
    int i, k, d, c, Cref, nBad = 0;
    if ( p->pCtx->pKind == NULL )
        Gip_CtxPrepareJftr( p->pCtx );   // a plain model of a solver that has not run the mode yet: the tables of the circuit, as the mode builds them
    pKind = p->pCtx->pKind;
    for ( d = 0; d < p->nVars; d++ )
    {
        if ( pKind[d] != GIP_KIND_NODE && pKind[d] != GIP_KIND_CO )
            continue;
        for ( c = pCnf->pObj2Clause[d]; c < pCnf->pObj2Clause[d] + pCnf->pObj2Count[d]; c++ )
            nBad += !Gip_VerClauseFlipped( p, pCnf->pClauses[c], (int)(pCnf->pClauses[c+1] - pCnf->pClauses[c]) );
    }
    for ( k = 0; k < 3; k++ )
        Vec_IntForEachEntry( vLists[k], Cref, i )
            if ( !Gip_ClaIsRemoved(&p->Cdb.Alloc, Cref) )
                nBad += !Gip_VerClauseFlipped( p, Gip_ClaLits(&p->Cdb.Alloc, Cref), Gip_ClaLen(&p->Cdb.Alloc, Cref) );
    p->Jftr.Ver.nFlip++;
    if ( nBad > 0 )
        Gip_JftrFatal( p, "PDR2_JFTR_CHECK=2: flip-to-none left a clause without a true literal" );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END

/**CFile****************************************************************

  FileName    [pdrMultiTimeframe.cpp]

  Synopsis    [Multi-timeframe PDR implementation.]

  Description [Extends PDR with multi-timeframe solving capability.
               When solving takes too long, automatically expands
               timeframe depth to improve convergence.]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "proof/pdr/pdrInt.h"
#include "StatisticsCollector.h"
#include "pdrProofObligationTreeLogger.h"  // runtime-guarded by use_proof_obligation_tree_logging
#include "pdrMultiTimeframe.h"

#include <iostream>
#include <vector>
#include <set>
#include <algorithm>
#include <cmath>
#include <cstdlib>

using std::vector;
using std::set;
using std::min;
using std::max;

// External declarations from pdrCore.c
extern "C" int Pdr_ManGeneralize( Pdr_Man_t * p, int k, Pdr_Set_t * pState, Pdr_Set_t ** ppPred, Pdr_Set_t ** ppCubeMin );
extern "C" void Pdr_ManCollectCone( Aig_Man_t * pAig, Vec_Int_t * vCoObjs, Vec_Int_t * vCiObjs, Vec_Int_t * vNodes );
extern "C" int Pdr_ManSimDataInit( Aig_Man_t * pAig, Vec_Int_t * vCiObjs, Vec_Int_t * vCiVals, Vec_Int_t * vNodes, Vec_Int_t * vCoObjs, Vec_Int_t * vCoVals, Vec_Int_t * vCi2Rem );
extern "C" int Pdr_ManExtendOne( Aig_Man_t * pAig, Aig_Obj_t * pObj, Vec_Int_t * vUndo, Vec_Int_t * vVisits );
extern "C" void Pdr_ManExtendUndo( Aig_Man_t * pAig, Vec_Int_t * vUndo );
extern "C" int * Pdr_ManSortByPriority( Pdr_Man_t * p, Pdr_Set_t * pCube );

// Global flag to enable/disable multi-timeframe PDR (pdr -s)
int use_multi_timeframe = 0;

// Fixed timeframe expansion (-E): every first-level query uses
// expansion = min(current kMax, this value), unconditionally from the start
// of every ManBlockCube call (no time-triggered restarts); -1 = dynamic (default)
int mtf_fixed_timeframe_expansion = -1;

//////////////////////////////////////////////////////////////////////////
// Multi-timeframe parameters
//
// Same control loop and defaults as rIC3-multi, only the env prefix
// differs. Every parameter can be overridden through its ABC_MT_*
// environment variable; parsing happens ONCE per process (thread-safe
// function-local static), the resolved values are printed once, and an
// unset or out-of-range value silently falls back to its default.
//////////////////////////////////////////////////////////////////////////

// structural bound: the unroll caches below are sized for this many frames
// (not tunable; ABC_MT_EXP_CAP may only lower the effective bound)
static const int MT_HARD_CAP = 80;

struct MtParams {
    // ABC_MT_MIN_LEVEL (default 4): mt intervenes only once the proof has
    // reached this frame; shallow triggers only confiscate the obligation
    // queue without buying depth
    int min_level;
    // ABC_MT_ABS_THRESHOLD_MS (default 10000): absolute "stuck" threshold in
    // milliseconds - an episode running longer than this (scaled by
    // abs_expand_factor per escalation) may trigger a restart (stored in
    // seconds)
    double abs_threshold_sec;
    // ABC_MT_MEDIAN_FACTOR (default 2): the episode must also exceed the
    // median episode time times this factor
    int median_factor;
    // ABC_MT_ABS_EXPAND_FACTOR (default 2.0): each escalation also
    // scales the absolute threshold (10s -> 20s -> 40s)
    double abs_expand_factor;
    // ABC_MT_EXP_RATIO (default 0.25, range [0,1]): ceiling ramp start -
    // at t=0 the expansion ceiling is ratio * kMax. 0.0 is legal and
    // meaningful (ceiling 1 = pure PDR opening); do not "validate" it away
    double ratio_start;
    // ABC_MT_RATIO_MAX (default 0.75, range [start,1]): ceiling ramp end
    double ratio_max;
    // ABC_MT_RATIO_RAMP_SEC (default 2400): linear ramp duration in seconds
    double ratio_ramp_sec;
    // ABC_MT_EXP_OVERSHOOT (default 2): earned ceiling doublings, shared
    // per frame (kMax)
    int overshoot_max;
    // ABC_MT_EXP_CAP (default off = -1): absolute expansion bound below the
    // structural cap; memory insurance
    int exp_cap;
    // ABC_MT_NEG_C_MID (default off, enable with any nonzero integer): also
    // place the anchored ~c on the intermediate unroll copies X(1)..X(l-1),
    // not only on X(0). Sound (an intermediate state in c would itself be a
    // shallower violation) and strictly stronger: more constraints make the
    // query UNSAT more often, so more literal drops are accepted, and the
    // solver prunes paths through c earlier. Never placed on X(l) - the
    // target must stay the full candidate d
    bool neg_c_mid;
    // ABC_MT_LOG (default off, enable with any nonzero integer): print one
    // line per SelectDepth event (breakthrough, restart) in the format
    // "TimeStamp = <seconds since run start, 2 decimals> : <event>"
    bool log;
};

static bool mt_env_double(const char* name, double* out) {
    const char* s = getenv(name);
    if (!s || !*s)
        return false;
    char* end = NULL;
    double v = strtod(s, &end);
    if (end == s || *end != '\0')
        return false;
    *out = v;
    return true;
}

static bool mt_env_int(const char* name, int* out) {
    const char* s = getenv(name);
    if (!s || !*s)
        return false;
    char* end = NULL;
    long v = strtol(s, &end, 10);
    if (end == s || *end != '\0')
        return false;
    *out = (int)v;
    return true;
}

static const MtParams& mt_params() {
    // C++11 magic static: initialized exactly once, on first use, with a
    // thread-safe guard; every later call is a single guard-flag check.
    static const MtParams params = [] {
        MtParams p;
        double d;
        int i;
        p.min_level = (mt_env_int("ABC_MT_MIN_LEVEL", &i) && i >= 0) ? i : 4;
        p.abs_threshold_sec =
            (mt_env_double("ABC_MT_ABS_THRESHOLD_MS", &d) && d >= 0.0) ? d / 1000.0 : 10.0;
        p.median_factor = (mt_env_int("ABC_MT_MEDIAN_FACTOR", &i) && i >= 0) ? i : 2;
        p.abs_expand_factor =
            (mt_env_double("ABC_MT_ABS_EXPAND_FACTOR", &d) && d > 0.0) ? d : 2.0;
        p.ratio_start =
            (mt_env_double("ABC_MT_EXP_RATIO", &d) && d >= 0.0 && d <= 1.0) ? d : 0.25;
        // the end may not undercut the start; with only EXP_RATIO set the
        // default end still keeps the ramp monotone
        p.ratio_max = (mt_env_double("ABC_MT_RATIO_MAX", &d) && d >= p.ratio_start && d <= 1.0)
                          ? d
                          : max(p.ratio_start, 0.75);
        p.ratio_ramp_sec = (mt_env_double("ABC_MT_RATIO_RAMP_SEC", &d) && d > 0.0) ? d : 2400.0;
        p.overshoot_max = (mt_env_int("ABC_MT_EXP_OVERSHOOT", &i) && i >= 0) ? i : 2;
        p.exp_cap = (mt_env_int("ABC_MT_EXP_CAP", &i) && i >= 1) ? i : -1;
        p.neg_c_mid = mt_env_int("ABC_MT_NEG_C_MID", &i) && i != 0;
        p.log = mt_env_int("ABC_MT_LOG", &i) && i != 0;
        // Print the resolved parameters once, in the shared cross-tool
        // format (env names without the tool prefix).
        Abc_Print(1, "\nMT params: MT_MIN_LEVEL=%d MT_ABS_THRESHOLD_MS=%g MT_MEDIAN_FACTOR=%d"
                     " MT_ABS_EXPAND_FACTOR=%g MT_EXP_RATIO=%g MT_RATIO_MAX=%g"
                     " MT_RATIO_RAMP_SEC=%g MT_EXP_OVERSHOOT=%d MT_EXP_CAP=",
                  p.min_level, p.abs_threshold_sec * 1000.0, p.median_factor,
                  p.abs_expand_factor, p.ratio_start, p.ratio_max,
                  p.ratio_ramp_sec, p.overshoot_max);
        if (p.exp_cap > 0)
            Abc_Print(1, "%d", p.exp_cap);
        else
            Abc_Print(1, "off");
        Abc_Print(1, " MT_NEG_C_MID=%s MT_LOG=%s\n", p.neg_c_mid ? "on" : "off",
                  p.log ? "on" : "off");
        return p;
    }();
    return params;
}

//////////////////////////////////////////////////////////////////////////
// Multi-timeframe manager class
//////////////////////////////////////////////////////////////////////////

struct MultiTimeframeManager {
    abctime start_time;   // episode timer (reset per episode and per restart)
    abctime run_start;    // PDR-run start: origin of the ceiling ramp
    Pdr_Set_t* pCube;
    int now_kMax;
    int current_expansion; // Alg. 3's l: expansion in force this episode (1 = standard PDR)
    double abs_mult;      // abs-threshold multiplier: abs_expand_factor^(escalations this episode)
    int overshoot_used;   // earned ceiling doublings (scoped to overshoot_level)
    int overshoot_level;  // kMax the allowance was earned at (-1 = none)
    BoundedMedianCalculator solving_time_median_collector;

    MultiTimeframeManager() :
        start_time(0),
        run_start(0),
        pCube(NULL),
        now_kMax(0),
        current_expansion(1),
        abs_mult(1.0),
        overshoot_used(0),
        overshoot_level(-1),
        solving_time_median_collector(1000, 0.2)  // max 1000 elements, remove 20% when full
    {}

    void reset() {
        if (pCube) {
            Pdr_SetDeref(pCube);
            pCube = NULL;
        }
    }

    // A new PDR run: reset the ramp origin, the median history and every
    // piece of episode/level state left over from the previous run.
    void on_run_start(abctime time) {
        run_start = time;
        start_time = time;
        current_expansion = 1;
        abs_mult = 1.0;
        overshoot_used = 0;
        overshoot_level = -1;
        solving_time_median_collector.reset();
        reset();
    }

    void init(abctime time, Pdr_Set_t* cube, int kMax) {
        start_time = time;
        current_expansion = 1;
        this->pCube = cube;
        Pdr_SetRef(cube);
        this->now_kMax = kMax;
        abs_mult = 1.0;                // abs-threshold patience resets with the episode
        if (overshoot_level != kMax) { // the earned allowance is per-frame:
            overshoot_used = 0;        // it survives episodes at the same kMax
            overshoot_level = -1;      // and resets when the frontier advances
        }
    }

    void restart(abctime time, Pdr_Man_t *p) {
        start_time = time;
        abs_mult *= mt_params().abs_expand_factor; // escalated queries get proportionally more time
        Pdr_QueueClean(p);
    }

    // Hard(f): the immovable expansion bound — kMax, the structural unroll
    // cap L (the caches are sized for it) and the optional ABC_MT_EXP_CAP.
    // Neither the ramp nor an earned overshoot can pass it; when the ceiling
    // sits on it, is_time_to_restart commits instead of spending overshoot
    // (a doubling would buy nothing).
    int hard_cap() const {
        const MtParams& mt = mt_params();
        int hard = min(now_kMax, MT_HARD_CAP);
        if (mt.exp_cap > 0)
            hard = min(hard, mt.exp_cap);
        return max(hard, 1);
    }

    // Seconds since the PDR-run start: the ramp clock, also the TimeStamp
    // origin of the ABC_MT_LOG event lines.
    double run_elapsed_sec(abctime time) const {
        return (1.0 * (time - run_start)) / CLOCKS_PER_SEC;
    }

    // Ceil(f): the deterministic time ramp ratio_start -> ratio_max of kMax
    // over ratio_ramp_sec, doubled per earned overshoot step, clamped by
    // hard_cap.
    int ceiling(abctime time) const {
        const MtParams& mt = mt_params();
        double frac = run_elapsed_sec(time) / mt.ratio_ramp_sec;
        if (frac > 1.0)
            frac = 1.0;
        const double ratio = mt.ratio_start + (mt.ratio_max - mt.ratio_start) * frac;
        const int base = max(1, (int)std::ceil(ratio * now_kMax));
        return min(hard_cap(), base << overshoot_used);
    }

    // The stuck condition: absolute (abs_expand_factor-scaled) AND relative-to-median.
    // An empty median counts as exceeded, so early episodes are gated by
    // the absolute threshold alone.
    bool is_under_pressure(const abctime& time) const {
        const MtParams& mt = mt_params();
        const double solving_time = (1.0 * (time - start_time)) / CLOCKS_PER_SEC;
        const bool abs_condition = mt.abs_threshold_sec * abs_mult < solving_time;
        const bool median_condition =
            solving_time_median_collector.is_empty() ||
            mt.median_factor * solving_time_median_collector.get_median() < solving_time;
        return abs_condition && median_condition;
    }

    // SelectDepth (Algorithm 3): decide whether the episode should deepen
    // its expansion and restart the attempt. Returns true when the caller
    // must clean the queue and re-seed the root. `timeframe_expansion`
    // aliases the caller's per-BlockCube expansion signal and is written
    // ONLY on a deepen, never reset: once an episode has escalated, every
    // top-level pop keeps blocking multi-frame at the current expansion.
    // Overshoot is spent only while a doubling actually buys room
    // (ceiling < hard_cap); hence a restart always strictly deepens, and
    // the deepened expansion is always >= 2 — for every config.
    bool is_time_to_restart(const abctime& time, int& timeframe_expansion) {
        if (!use_multi_timeframe) {
            return false;
        }
        // Fixed expansion mode (-E): the expansion is applied unconditionally
        // at ManBlockCube entry; time-triggered restarts are disabled.
        if (mtf_fixed_timeframe_expansion > 0) {
            return false;
        }
        const MtParams& mt = mt_params();
        if (now_kMax < mt.min_level) {
            return false;
        }

        // Easy: no expansion needed.
        if (!is_under_pressure(time)) {
            return false;
        }

        // At the ceiling: breakthrough or commit. Invariant: expansion <=
        // ceiling — the expansion is only ever assigned min(.., ceiling),
        // and the ceiling is non-decreasing while the expansion persists
        // (ramp up, overshoot up, kMax fixed) — hence the equality test.
        const int c = ceiling(time);
        assert(current_expansion <= c);
        if (current_expansion == c) {
            if (overshoot_used >= mt.overshoot_max || c == hard_cap()) {
                // Out of breakthroughs, or the wall is immovable (hard cap:
                // a doubling would buy nothing): commit — keep blocking
                // multi-frame at the capped expansion.
                return false;
            }
            // Breakthrough: ceiling < hard_cap, so the earned doubling
            // (shared by later episodes at the same kMax) strictly raises
            // it and the deepen below strictly deepens.
            overshoot_used++;
            overshoot_level = now_kMax;
            if (mt.log)
                Abc_Print(1, "\nTimeStamp = %.2f : update b from %d to %d\n",
                          run_elapsed_sec(time), overshoot_used - 1, overshoot_used);
        }

        // Deepen and restart the attempt; the ceiling is recomputed with any
        // overshoot just granted. The budget doubling lives in restart():
        // abs_mult *= abs_expand_factor, and the episode timer resets.
        current_expansion = min(2 * current_expansion, ceiling(time));
        timeframe_expansion = current_expansion;
        if (mt.log)
            Abc_Print(1, "\nTimeStamp = %.2f : restarting with expansion = %d\n",
                      run_elapsed_sec(time), current_expansion);
        return true;
    }

    void add_solving_time(double solving_time) {
        // BoundedMedianCalculator automatically removes outliers when at capacity
        solving_time_median_collector.add_value(solving_time);
    }
};

// Global multi-timeframe manager instance
static MultiTimeframeManager multi_timeframe_manager;

//////////////////////////////////////////////////////////////////////////
// SolvingData struct for multi-timeframe SAT solving
//////////////////////////////////////////////////////////////////////////

struct SolvingData {
    sat_solver* pSat;
    Aig_Man_t* pAig;
    Cnf_Dat_t* pCnf;
    vector<int> Id2Vars;
    vector<int> Var2Ids;
    int k;
    int timeframe_expansion;

    SolvingData() : pSat(NULL), pAig(NULL), pCnf(NULL), k(-1), 
                    timeframe_expansion(-1) {}
    
    SolvingData(sat_solver* sat, Aig_Man_t* aig, Cnf_Dat_t* cnf, int frame, int tf_exp) 
        : pSat(sat), pAig(aig), pCnf(cnf), k(frame), 
          timeframe_expansion(tf_exp) {
        Id2Vars.resize(Aig_ManObjNumMax(aig), -1);
        Var2Ids.reserve(500);
        Var2Ids.push_back(-1);
    }
};

//////////////////////////////////////////////////////////////////////////
// Multi-timeframe namespace for AIG/CNF management
//////////////////////////////////////////////////////////////////////////

namespace multiTimeframe {
    const int L = 80;  // Maximum timeframe expansion
    
    int pi_num = 0;
    int reg_num = 0;
    int po_num = 1;
    bool initialized = false;

    vector<Aig_Man_t*> pAig_vec(L+1, nullptr);
    vector<Cnf_Man_t*> pCnfMan_vec(L+1, nullptr);
    vector<Cnf_Dat_t*> pCnf_vec(L+1, nullptr);
    sat_solver *pSat = nullptr;

    bool is_pi_by_CiId(int CiId) {
        return CiId < pi_num || pi_num + reg_num <= CiId;
    }

    int get_reg_index_from_CoId(int CoId, int f) {
        return CoId - (reg_num + po_num) * (f - 1) - po_num;
    }

    int get_CoId_from_reg_index(int reg_index, int f) {
        return (reg_num + po_num) * (f - 1) + po_num + reg_index;
    }
}

//////////////////////////////////////////////////////////////////////////
// Helper functions
//////////////////////////////////////////////////////////////////////////

static double abctime_to_seconds(abctime time) {
    return (1.0 * time) / CLOCKS_PER_SEC;
}

//////////////////////////////////////////////////////////////////////////
// Multi-timeframe AIG construction
//////////////////////////////////////////////////////////////////////////

static Aig_Man_t* PdrMultiTimeframe_create_aig_with_internal_registers_as_Po(Pdr_Man_t *p, int nFrames) {
    Aig_Obj_t* pObj;
    Aig_Obj_t* pObjLi;
    Aig_Obj_t* pObjLo;
    int i;
    Aig_Man_t* pSAig = p->pAig;
    Aig_Man_t* pCAig = Aig_ManStart(Aig_ManNodeNum(pSAig) * nFrames);
    
    Aig_Obj_t* pObjCi;
    int CiId = 0;
    int CoId = 0;

    Aig_ManConst1(pSAig)->pData = Aig_ManConst1(pCAig);
    Aig_ManForEachCi(pSAig, pObj, i) {
        pObjCi = Aig_ObjCreateCi(pCAig);
        pObjCi->CioId = CiId++;
        pObj->pData = pObjCi;
    }
    
    for (int f = 1; f <= nFrames; ++f) {
        if (f != 1) {
            Saig_ManForEachPi(pSAig, pObj, i) {
                pObjCi = Aig_ObjCreateCi(pCAig);
                pObjCi->CioId = CiId++;
                pObj->pData = pObjCi;
            }
        }
        
        Aig_ManForEachNode(pSAig, pObj, i) {
            pObj->pData = Aig_And(pCAig, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
        }
        
        Aig_ManForEachCo(pSAig, pObj, i) {
            Aig_ObjCreateCo(pCAig, Aig_ObjChild0Copy(pObj))->CioId = CoId++;
        }
        
        if (f == nFrames)
            break;

        Saig_ManForEachLi(pSAig, pObj, i)
            pObj->pData = Aig_ObjChild0Copy(pObj);
        Saig_ManForEachLiLo(pSAig, pObjLi, pObjLo, i)
            pObjLo->pData = pObjLi->pData;
    }
    Aig_ManCleanup(pCAig);

    return pCAig;
}

static Aig_Man_t* PdrMultiTimeframe_create_aig(Pdr_Man_t *p, int timeframe_expansion) {
    assert(!p->pPars->fMonoCnf);
    return PdrMultiTimeframe_create_aig_with_internal_registers_as_Po(p, timeframe_expansion);
}

static Aig_Man_t* get_pAig(Pdr_Man_t *p, int timeframe_expansion) {
    assert(timeframe_expansion >= 0 && timeframe_expansion <= multiTimeframe::L);
    if (multiTimeframe::pAig_vec[timeframe_expansion] == nullptr) {
        multiTimeframe::pAig_vec[timeframe_expansion] = PdrMultiTimeframe_create_aig(p, timeframe_expansion);
        multiTimeframe::pCnfMan_vec[timeframe_expansion] = Cnf_ManStart();
        multiTimeframe::pCnf_vec[timeframe_expansion] = Cnf_DeriveOtherWithMan(
            multiTimeframe::pCnfMan_vec[timeframe_expansion], 
            multiTimeframe::pAig_vec[timeframe_expansion], 0);
    }
    return multiTimeframe::pAig_vec[timeframe_expansion];
}

//////////////////////////////////////////////////////////////////////////
// Initialization
//////////////////////////////////////////////////////////////////////////

static void PdrMultiTimeframe_init(Pdr_Man_t *p) {
    multiTimeframe::pi_num = Saig_ManPiNum(p->pAig);
    multiTimeframe::reg_num = Saig_ManRegNum(p->pAig);
    multiTimeframe::initialized = true;
}

// Called from Pdr_ManStart at the beginning of every PDR run: reset the
// restart controller (ramp origin, median history, abs multiplier, overshoot
// allowance) and drop the unrolled AIG/CNF/solver caches — they were built
// for the previous network and reusing them on a different AIG would be
// unsound.
extern "C" void PdrMultiTimeframe_OnRunStart(void) {
    multi_timeframe_manager.on_run_start(Abc_Clock());
    for (int t = 0; t <= multiTimeframe::L; ++t) {
        if (multiTimeframe::pCnf_vec[t]) {
            Cnf_DataFree(multiTimeframe::pCnf_vec[t]);
            multiTimeframe::pCnf_vec[t] = nullptr;
        }
        if (multiTimeframe::pCnfMan_vec[t]) {
            Cnf_ManStop(multiTimeframe::pCnfMan_vec[t]);
            multiTimeframe::pCnfMan_vec[t] = nullptr;
        }
        if (multiTimeframe::pAig_vec[t]) {
            Aig_ManStop(multiTimeframe::pAig_vec[t]);
            multiTimeframe::pAig_vec[t] = nullptr;
        }
    }
    if (multiTimeframe::pSat) {
        sat_solver_delete(multiTimeframe::pSat);
        multiTimeframe::pSat = nullptr;
    }
    multiTimeframe::initialized = false;
}

//////////////////////////////////////////////////////////////////////////
// SAT variable management
//////////////////////////////////////////////////////////////////////////

static inline int PdrMultiTimeframe_ObjSatVarFindOrAdd(Pdr_Man_t *p, SolvingData& solving_data, 
                                                        Aig_Obj_t *pObj, int *pfNewVar) { 
    assert(solving_data.pCnf->pObj2Count[Aig_ObjId(pObj)] >= 0);
    if (solving_data.Id2Vars[Aig_ObjId(pObj)] == -1) {
        int iVarNew = solving_data.Var2Ids.size();
        assert(iVarNew > 0);
        solving_data.Var2Ids.push_back(Aig_ObjId(pObj));
        solving_data.Id2Vars[Aig_ObjId(pObj)] = iVarNew;
        sat_solver_setnvars(solving_data.pSat, iVarNew + 1);

        const bool reach_initial_state = solving_data.k - solving_data.timeframe_expansion == 0;
        const bool is_initial_register = (multiTimeframe::pi_num < Aig_ObjId(pObj) && 
                                          Aig_ObjId(pObj) <= multiTimeframe::pi_num + multiTimeframe::reg_num);
        if (reach_initial_state && is_initial_register) {
            int Lit = Abc_Var2Lit(iVarNew, 1);
            int RetValue = sat_solver_addclause(solving_data.pSat, &Lit, &Lit + 1);
            assert(RetValue == 1);
            (void)RetValue;
            sat_solver_compress(solving_data.pSat);
        }
        *pfNewVar = 1;
    }
    return solving_data.Id2Vars[Aig_ObjId(pObj)];
}

static int PdrMultiTimeframe_ObjSatVar(Pdr_Man_t *p, SolvingData& solving_data, Aig_Obj_t *pObj, int Level) {
    Vec_Int_t *vLits;
    sat_solver *pSat;
    int fNewVar = 0, iVarThis = PdrMultiTimeframe_ObjSatVarFindOrAdd(p, solving_data, pObj, &fNewVar);

    int *pLit, i, iVar, iClaBeg, iClaEnd, RetValue;
    if (Aig_ObjIsCi(pObj) || !fNewVar)
        return iVarThis;
        
    iClaBeg = solving_data.pCnf->pObj2Clause[Aig_ObjId(pObj)];
    iClaEnd = iClaBeg + solving_data.pCnf->pObj2Count[Aig_ObjId(pObj)];
    assert(iClaBeg < iClaEnd);
    pSat = solving_data.pSat;
    vLits = Vec_WecEntry(p->vVLits, Level);
    
    for (i = iClaBeg; i < iClaEnd; i++) {
        Vec_IntClear(vLits);
        Vec_IntPush(vLits, Abc_Var2Lit(iVarThis, Abc_LitIsCompl(solving_data.pCnf->pClauses[i][0])));
        for (pLit = solving_data.pCnf->pClauses[i]+1; pLit < solving_data.pCnf->pClauses[i+1]; pLit++) {
            iVar = PdrMultiTimeframe_ObjSatVar(p, solving_data, 
                                                Aig_ManObj(solving_data.pAig, Abc_Lit2Var(*pLit)), Level+1);
            Vec_IntPush(vLits, Abc_Var2Lit(iVar, Abc_LitIsCompl(*pLit)));
        }
        RetValue = sat_solver_addclause(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits)+Vec_IntSize(vLits));
        assert(RetValue);
        (void)RetValue;
    }
    return iVarThis;
}

//////////////////////////////////////////////////////////////////////////
// Cube to literals conversion
//////////////////////////////////////////////////////////////////////////

static Vec_Int_t* PdrMultiTimeframe_ManCubeToLits_at_frame(Pdr_Man_t *p, SolvingData& solving_data, 
                                                           Pdr_Set_t *pCube, int fCompl, int k) {
    Aig_Obj_t *pObj;
    int i, iVar, iVarMax = 0;
    abctime clk = Abc_Clock();
    Vec_IntClear(p->vLits);
    const int start_frame = solving_data.k - solving_data.timeframe_expansion;
    assert(start_frame <= k && k <= solving_data.k);

    for (i = 0; i < pCube->nLits; i++) {
        if (pCube->Lits[i] == -1)
            continue;
        const int reg_index = Abc_Lit2Var(pCube->Lits[i]);
        if (k == start_frame)
            pObj = Aig_ManCi(solving_data.pAig, multiTimeframe::pi_num + reg_index);
        else {
            const int coId = multiTimeframe::get_CoId_from_reg_index(reg_index, k - start_frame);
            pObj = Aig_ManCo(solving_data.pAig, coId);
        }
        iVar = PdrMultiTimeframe_ObjSatVar(p, solving_data, pObj, 0);
        assert(iVar >= 0);
        iVarMax = Abc_MaxInt(iVarMax, iVar);
        Vec_IntPush(p->vLits, Abc_Var2Lit(iVar, fCompl ^ Abc_LitIsCompl(pCube->Lits[i])));
    }

    p->tCnf += Abc_Clock() - clk;
    return p->vLits;
}

static Vec_Int_t* PdrMultiTimeframe_ManCubeToLits(Pdr_Man_t *p, Pdr_Set_t *pCube, 
                                                   SolvingData& solving_data, int fCompl, int fNext) {
    if (fNext)
        return PdrMultiTimeframe_ManCubeToLits_at_frame(p, solving_data, pCube, fCompl, solving_data.k);
    else
        return PdrMultiTimeframe_ManCubeToLits_at_frame(p, solving_data, pCube, fCompl, 
                                                        solving_data.k - solving_data.timeframe_expansion);
}

//////////////////////////////////////////////////////////////////////////
// Anchored negated side of the multi-timeframe query
//////////////////////////////////////////////////////////////////////////

// Every query in the l-step generalization is
//     SAT? [ ~c(X(0)) & Unroll(f,l) & d(X(l)) ]
// where c is the obligation cube this call started from and d is the current
// candidate. Only the target side follows d; the negated side is pinned to c
// for the whole call, so it is added here once, before any literal is dropped.
//
// Letting the negated side track d (~d, as standard PDR does at l == 1) is
// wrong for l >= 2: dropping literals makes d weaker as a cube but larger as
// a state set, so ~d is a *stronger* constraint than ~c, and the l-step query
// only samples the state every l steps. A path whose first entry into d
// happens inside the window has its only witness starting inside d, where
// ~d(X(0)) rules it out - so UNSAT can coexist with a reachable state in d
// and the learned clause then excludes a reachable state from the frames.
// Anchoring on c closes that: such an escaping state either lies in c (then it
// is itself a shallower violation, killed by minimality of the violation
// depth) or it satisfies ~c(X(0)) and is a legal witness, contradicting UNSAT.
//
// With ABC_MT_NEG_C_MID the same ~c also goes on the intermediate copies
// X(1)..X(l-1): sound by the same minimality argument and strictly stronger.
// Never on X(l) - the target must stay the full d.
//
// The clauses are added unconditionally (no activation literal): the solver is
// rebuilt per obligation in PdrMultiTimeframe_ManGetSolvingData, so they
// cannot leak into another obligation's queries.
static void PdrMultiTimeframe_ManAddAnchoredNegC(Pdr_Man_t *p, SolvingData& solving_data,
                                                 Pdr_Set_t *pCube) {
    const int start_frame = solving_data.k - solving_data.timeframe_expansion;
    const int last_frame = mt_params().neg_c_mid ? solving_data.k - 1 : start_frame;
    assert(start_frame <= last_frame && last_frame < solving_data.k);

    for (int f = start_frame; f <= last_frame; ++f) {
        Vec_Int_t *vLits = PdrMultiTimeframe_ManCubeToLits_at_frame(p, solving_data, pCube, 1, f);
        const int RetValue = sat_solver_addclause(solving_data.pSat, Vec_IntArray(vLits),
                                                  Vec_IntArray(vLits) + Vec_IntSize(vLits));
        // ~c can only be refuted at decision level 0 if the initial state
        // satisfies c, and an init-intersecting obligation never reaches here
        assert(RetValue == 1);
        (void)RetValue;
    }
    sat_solver_compress(solving_data.pSat);
}

//////////////////////////////////////////////////////////////////////////
// Register number extraction
//////////////////////////////////////////////////////////////////////////

static int PdrMultiTimeframe_ObjRegNum(Pdr_Man_t *p, SolvingData& solving_data, int iSatVar) {
    Aig_Obj_t *pObj;
    int ObjId;
    assert(iSatVar > 0 && iSatVar < (int)solving_data.Var2Ids.size());
    ObjId = solving_data.Var2Ids[iSatVar];
    if (ObjId == -1)
        return -1;
    pObj = Aig_ManObj(solving_data.pAig, ObjId);
    if (Aig_ObjIsCo(pObj)) {
        const int coId = Aig_ObjCioId(pObj);
        assert((multiTimeframe::reg_num + multiTimeframe::po_num) * (solving_data.timeframe_expansion - 1) < coId);
        return multiTimeframe::get_reg_index_from_CoId(coId, solving_data.timeframe_expansion);
    }
    assert(0);
    return -1;
}

static Vec_Int_t* PdrMultiTimeframe_ManLitsToCube(Pdr_Man_t *p, SolvingData& solving_data, 
                                                   int *pArray, int nArray) {
    int i, RegId;
    Vec_IntClear(p->vLits);
    for (i = 0; i < nArray; i++) {
        RegId = PdrMultiTimeframe_ObjRegNum(p, solving_data, Abc_Lit2Var(pArray[i]));
        if (RegId == -1)
            continue;
        assert(RegId >= 0 && RegId < multiTimeframe::reg_num);
        Vec_IntPush(p->vLits, Abc_Var2Lit(RegId, !Abc_LitIsCompl(pArray[i])));
    }
    assert(Vec_IntSize(p->vLits) >= 0 && Vec_IntSize(p->vLits) <= nArray);
    return p->vLits;
}

//////////////////////////////////////////////////////////////////////////
// Clause reduction
//////////////////////////////////////////////////////////////////////////

static Pdr_Set_t* PdrMultiTimeframe_ManReduceClause(Pdr_Man_t *p, Pdr_Set_t *pCube, SolvingData& solving_data) {
    Pdr_Set_t *pCubeMin;
    Vec_Int_t *vLits;
    int i, Entry, nCoreLits, *pCoreLits;
    
    nCoreLits = sat_solver_final(solving_data.pSat, &pCoreLits);
    vLits = PdrMultiTimeframe_ManLitsToCube(p, solving_data, pCoreLits, nCoreLits);

    if (Vec_IntSize(vLits) == pCube->nLits)
        return NULL;
    assert(Vec_IntSize(vLits) < pCube->nLits);
    
    Vec_IntForEachEntry(vLits, Entry, i)
        if (Abc_LitIsCompl(Entry) == 0)
            break;
    if (i == Vec_IntSize(vLits)) {
        for (i = 0; i < pCube->nLits; i++)
            if (Abc_LitIsCompl(pCube->Lits[i]) == 0) {
                Vec_IntPush(vLits, pCube->Lits[i]);
                break;
            }
        assert(i < pCube->nLits);
    }
    
    pCubeMin = Pdr_SetCreateSubset(pCube, Vec_IntArray(vLits), Vec_IntSize(vLits));
    assert(!Pdr_SetIsInit(pCubeMin, -1));
    return pCubeMin;
}

//////////////////////////////////////////////////////////////////////////
// Ternary simulation for multi-timeframe
//////////////////////////////////////////////////////////////////////////

static void PdrMultiTimeframe_ManCollectValues(Pdr_Man_t *p, SolvingData& solving_data, 
                                                Vec_Int_t *vObjIds, Vec_Int_t *vValues) {
    Aig_Obj_t *pObj;
    int iVar, i;
    Vec_IntClear(vValues);
    Aig_ManForEachObjVec(vObjIds, solving_data.pAig, pObj, i) {
        iVar = PdrMultiTimeframe_ObjSatVar(p, solving_data, pObj, 0);
        assert(iVar >= 0);
        Vec_IntPush(vValues, sat_solver_var_value(solving_data.pSat, iVar));
    }
}

static void PdrMultiTimeframe_ManCollectTernarySimData(Pdr_Man_t *p, Pdr_Set_t *pCube, SolvingData& solving_data) {
    Vec_Int_t *vCiObjs = p->vCiObjs;
    Vec_Int_t *vCoObjs = p->vCoObjs;
    Vec_Int_t *vCiVals = p->vCiVals;
    Vec_Int_t *vCoVals = p->vCoVals;
    Vec_Int_t *vNodes = p->vNodes;
    Aig_Obj_t *pObj;
    int i;

    Vec_IntClear(vCoObjs);
    assert(pCube != NULL);

    for (i = 0; i < pCube->nLits; i++) {
        if (pCube->Lits[i] == -1)
            continue;
        const int reg_index = (pCube->Lits[i] >> 1);
        const int coId = multiTimeframe::get_CoId_from_reg_index(reg_index, solving_data.timeframe_expansion);
        pObj = Aig_ManCo(solving_data.pAig, coId);
        Vec_IntPush(vCoObjs, Aig_ObjId(pObj));
    }
    
    Pdr_ManCollectCone(solving_data.pAig, vCoObjs, vCiObjs, vNodes);
    PdrMultiTimeframe_ManCollectValues(p, solving_data, vCiObjs, vCiVals);
    PdrMultiTimeframe_ManCollectValues(p, solving_data, vCoObjs, vCoVals);
}

static void PdrMultiTimeframe_ManDeriveResult(Aig_Man_t *pAig, Vec_Int_t *vCiObjs, Vec_Int_t *vCiVals, 
                                               Vec_Int_t *vCi2Rem, Vec_Int_t *vRes, Vec_Int_t *vPiLits) {
    Aig_Obj_t *pObj;
    int i, Var, Lit;
    // mark removed flop outputs
    Aig_ManIncrementTravId(pAig);
    Aig_ManForEachObjVec(vCi2Rem, pAig, pObj, i) {
        assert(!multiTimeframe::is_pi_by_CiId(Aig_ObjCioId(pObj)));
        Aig_ObjSetTravIdCurrent(pAig, pObj);
    }
    // collect flop outputs that are not marked
    Vec_IntClear(vRes);
    Vec_IntClear(vPiLits);
    Aig_ManForEachObjVec(vCiObjs, pAig, pObj, i) {
        const int ciId = Aig_ObjCioId(pObj);
        // var: pi index or reg index

        if (multiTimeframe::is_pi_by_CiId(ciId)) { 
            Var = ciId < multiTimeframe::pi_num + multiTimeframe::reg_num ? ciId : ciId - multiTimeframe::reg_num;
            Lit = Abc_Var2Lit(Var, (Vec_IntEntry(vCiVals, i) == 0));
            Vec_IntPush(vPiLits, Lit);
            continue;
        }
        if (Aig_ObjIsTravIdCurrent(pAig, pObj))
            continue;

        Var = ciId - multiTimeframe::pi_num;
        Lit = Abc_Var2Lit(Var, (Vec_IntEntry(vCiVals, i) == 0));
        Vec_IntPush(vRes, Lit);
    }
    if (Vec_IntSize(vRes) == 0)
        Vec_IntPush(vRes, 0);
}

static Pdr_Set_t* PdrMultiTimeframe_ManTernarySim_internal(Pdr_Man_t *p, Aig_Man_t *pAig, int timeframe_expansion) {
    Pdr_Set_t *pRes;
    Vec_Int_t *vPrio = p->vPrio;
    Vec_Int_t *vPiLits = p->vLits;
    Vec_Int_t *vCiObjs = p->vCiObjs;
    Vec_Int_t *vCiVals = p->vCiVals;
    Vec_Int_t *vCoObjs = p->vCoObjs;
    Vec_Int_t *vCoVals = p->vCoVals;
    Vec_Int_t *vNodes = p->vNodes;
    Vec_Int_t *vUndo = p->vUndo;
    Vec_Int_t *vVisits = p->vVisits;
    Vec_Int_t *vCi2Rem = p->vCi2Rem;
    Vec_Int_t *vRes = p->vRes;
    Aig_Obj_t *pObj;
    int i, Entry, RetValue;

    if (pAig->pTerSimData == NULL)
        pAig->pTerSimData = ABC_CALLOC(unsigned, 1 + (Aig_ManObjNumMax(pAig) / 16));
    if (pAig->pFanData == NULL)
        Aig_ManFanoutStart(pAig);

    RetValue = Pdr_ManSimDataInit(pAig, vCiObjs, vCiVals, vNodes, vCoObjs, vCoVals, NULL);
    assert(RetValue);
    (void)RetValue;

    // iteratively remove flops

    // try removing low-priority flops first
    Vec_IntClear(vCi2Rem);
    Aig_ManForEachObjVec(vCiObjs, pAig, pObj, i) {
        const int ciId = Aig_ObjCioId(pObj);
        if (multiTimeframe::is_pi_by_CiId(ciId)) 
            continue;

        Entry = ciId - multiTimeframe::pi_num;
        if (Vec_IntEntry(vPrio, Entry))
            continue;
        Vec_IntClear(vUndo);
        if (Pdr_ManExtendOne(pAig, pObj, vUndo, vVisits))
            Vec_IntPush(vCi2Rem, Aig_ObjId(pObj));
        else
            Pdr_ManExtendUndo(pAig, vUndo);
    }
    // try removing high-priority flops next
    Aig_ManForEachObjVec(vCiObjs, pAig, pObj, i) {
        const int ciId = Aig_ObjCioId(pObj);
        if (multiTimeframe::is_pi_by_CiId(ciId)) 
            continue;
        
        Entry = ciId - multiTimeframe::pi_num;
        if (!Vec_IntEntry(vPrio, Entry))
            continue;
        Vec_IntClear(vUndo);
        if (Pdr_ManExtendOne(pAig, pObj, vUndo, vVisits))
            Vec_IntPush(vCi2Rem, Aig_ObjId(pObj));
        else
            Pdr_ManExtendUndo(pAig, vUndo);
    }

    RetValue = Pdr_ManSimDataInit(pAig, vCiObjs, vCiVals, vNodes, vCoObjs, vCoVals, vCi2Rem);
    assert(RetValue);
    (void)RetValue;

    PdrMultiTimeframe_ManDeriveResult(pAig, vCiObjs, vCiVals, vCi2Rem, vRes, vPiLits);
    assert(Vec_IntSize(vRes) > 0);

    // Use negative number to distinguish multi-timeframe proof-obligation
    Vec_IntPush(vPiLits, -timeframe_expansion);
    pRes = Pdr_SetCreate(vRes, vPiLits);
    return pRes;
}

static Pdr_Set_t* PdrMultiTimeframe_ManTernarySim(Pdr_Man_t *p, SolvingData& solving_data, Pdr_Set_t *pCube) {
    PdrMultiTimeframe_ManCollectTernarySimData(p, pCube, solving_data);
    return PdrMultiTimeframe_ManTernarySim_internal(p, solving_data.pAig, solving_data.timeframe_expansion);
}

//////////////////////////////////////////////////////////////////////////
// Multi-timeframe check cube
//////////////////////////////////////////////////////////////////////////

// Assumptions are the target side only: d(X(l)). The negated side ~c is a
// permanent clause of this obligation's solver, installed once by
// PdrMultiTimeframe_ManAddAnchoredNegC, so it does NOT follow the shrinking
// candidate d.
static int PdrMultiTimeframe_ManCheckCube(Pdr_Man_t *p, Pdr_Set_t *pCube, SolvingData& solving_data,
                                           Pdr_Set_t **ppPred, int nConfLimit, int fTryConf) {
    Vec_Int_t *vLits;
    int RetValue;
    abctime clk, Limit;
    p->nCalls++;

    vLits = PdrMultiTimeframe_ManCubeToLits(p, pCube, solving_data, 0, 1);

    clk = Abc_Clock();
    Limit = sat_solver_set_runtime_limit(solving_data.pSat, Pdr_ManTimeLimit(p));
    RetValue = sat_solver_solve(solving_data.pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), 
                                fTryConf ? p->pPars->nConfGenLimit : nConfLimit, 0, 0, 0);
    sat_solver_set_runtime_limit(solving_data.pSat, Limit);

    if (RetValue == l_Undef) {
        if (fTryConf && p->pPars->nConfGenLimit)
            RetValue = l_True;
        else
            return -1;
    }

    clk = Abc_Clock() - clk;
    p->tSat += clk;
    assert(RetValue != l_Undef);
    
    if (RetValue == l_False) {
        p->tSatUnsat += clk;
        p->nCallsU++;
        if (ppPred)
            *ppPred = NULL;
        RetValue = 1;
    } else {
        p->tSatSat += clk;
        p->nCallsS++;
        if (ppPred) {
            abctime clk2 = Abc_Clock();
            *ppPred = PdrMultiTimeframe_ManTernarySim(p, solving_data, pCube);
            p->tTsim += Abc_Clock() - clk2;
            p->nXsimLits += (*ppPred)->nLits;
            p->nXsimRuns++;
        }
        RetValue = 0;
    }
    return RetValue;
}

//////////////////////////////////////////////////////////////////////////
// Multi-timeframe generalize
//////////////////////////////////////////////////////////////////////////

static int PdrMultiTimeframe_ManGeneralize(Pdr_Man_t *p, Pdr_Set_t *pCube, SolvingData& solving_data, 
                                            Pdr_Set_t **ppPred, Pdr_Set_t **ppCubeMin) {
    Pdr_Set_t *pCubeMin, *pCubeTmp = NULL;
    int i, j, Lit, RetValue;
    abctime clk = Abc_Clock();
    int *pOrder;
    
    *ppCubeMin = NULL;
    // Pin the negated side to the obligation cube before anything is dropped:
    // every query below is  ~c(X(0)) & Unroll & d(X(l)),  with only d moving.
    PdrMultiTimeframe_ManAddAnchoredNegC(p, solving_data, pCube);
    RetValue = PdrMultiTimeframe_ManCheckCube(p, pCube, solving_data, ppPred, p->pPars->nConfLimit, 0);

    if (RetValue == -1)
        return -1;
    if (RetValue == 0) {
        p->tGeneral += Abc_Clock() - clk;
        return 0;
    }

    pCubeMin = PdrMultiTimeframe_ManReduceClause(p, pCube, solving_data);
    if (pCubeMin == NULL)
        pCubeMin = Pdr_SetDup(pCube);

    if (!p->pPars->fSkipGeneral) {
        pOrder = Pdr_ManSortByPriority(p, pCubeMin);
        for (j = 0; j < pCubeMin->nLits; j++) {
            i = pOrder[j];

            assert(pCubeMin->Lits[i] != -1);
            if (Pdr_SetIsInit(pCubeMin, i))
                continue;

            Lit = pCubeMin->Lits[i]; 
            pCubeMin->Lits[i] = -1;
            RetValue = PdrMultiTimeframe_ManCheckCube(p, pCubeMin, solving_data, NULL, p->pPars->nConfLimit, 1);

            if (RetValue == -1) {
                Pdr_SetDeref(pCubeMin);
                return -1;
            }
            pCubeMin->Lits[i] = Lit;
            if (RetValue == 0)
                continue;

            pCubeMin = Pdr_SetCreateFrom(pCubeTmp = pCubeMin, i);
            Pdr_SetDeref(pCubeTmp);
            assert(pCubeMin->nLits > 0);

            pOrder = Pdr_ManSortByPriority(p, pCubeMin);
            j--;
        }
    }

    *ppCubeMin = pCubeMin;
    p->tGeneral += Abc_Clock() - clk;
    return 1;
}

//////////////////////////////////////////////////////////////////////////
// Recursive refinement
//////////////////////////////////////////////////////////////////////////

// Block `pCube` at the short horizon k with standard 1-step recursive
// blocking, so states reachable in fewer than the full expansion — invisible
// to the exact-k query — are covered.
// Returns  1: refined (clauses added to frames 1..k; the outermost call also
//             hands the refined core back through *ppCore, referenced)
//          0: the state is reachable within the horizon — the mt path must
//             abort and report the counterexample instead of blocking
//         -1: a resource limit fired inside generalization
// Both non-1 results MUST propagate through the recursion: swallowing the
// inner result (or falling through with pCubeMin == NULL on the -1 path)
// would add a NULL clause or, worse, turn a resource limit into a bogus
// "counterexample found".
static int PdrMultiTimeframe_ManRecRefine(Pdr_Man_t *p, Pdr_Set_t *pCube, int k,
                                          Pdr_Set_t **ppCore, bool is_rec) {
    assert(k >= 1);
    Pdr_Set_t *pPred, *pCubeMin;
    int RetValue;
    pCubeMin = NULL;

    while ((RetValue = Pdr_ManGeneralize(p, k-1, pCube, &pPred, &pCubeMin)) == 0) {
        // SAT
        if (p->pPars->fShortest) {
            assert(k > 1);
        } else {
            if (k == 1) {
                return 0;
            }
        }
        const int inner = PdrMultiTimeframe_ManRecRefine(p, pPred, k-1, NULL, true);
        if (inner != 1) {
            return inner;
        }
    }
    if (RetValue == -1) {
        return -1;
    }

    for (int i = 1; i <= k; ++i) {
        Pdr_ManSolverAddClause(p, i, pCubeMin);
    }
    Vec_VecPush(p->vClauses, k, pCubeMin);

    if (!is_rec && ppCore) {
        Pdr_SetRef(pCubeMin);
        *ppCore = pCubeMin;
    }
    return 1;
}

static Pdr_Set_t* PdrMultiTimeframe_ManGet_blocking_cube(Pdr_Man_t *p, Pdr_Set_t *pCubeMin, Pdr_Set_t *unsat_core_l_1) {
    set<int> s;
    for (int i = 0; i < pCubeMin->nLits; ++i) {
        s.insert(pCubeMin->Lits[i]);
    }
    for (int i = 0; i < unsat_core_l_1->nLits; ++i) {
        s.insert(unsat_core_l_1->Lits[i]);
        assert(s.find(lit_neg(unsat_core_l_1->Lits[i])) == s.end());
    }
    
    Vec_Int_t* vRes = p->vRes;
    Vec_IntClear(vRes);
    for (auto it = s.begin(); it != s.end(); ++it) {
        Vec_IntPush(vRes, *it);
    }
    Vec_Int_t* dummy_pi = p->vLits;
    Vec_IntClear(dummy_pi);
    return Pdr_SetCreate(vRes, dummy_pi);
}

//////////////////////////////////////////////////////////////////////////
// Property output setting
//////////////////////////////////////////////////////////////////////////

static void PdrMultiTimeframe_ManSetPropertyOutput(Pdr_Man_t *p, SolvingData& solving_data) {
    const int timeframe_expansion = solving_data.timeframe_expansion;
    sat_solver *pSat = solving_data.pSat;
    
    for (int f = 1; f <= timeframe_expansion; ++f) {
        const int ith_co = (multiTimeframe::reg_num + multiTimeframe::po_num) * (f - 1);
        Aig_Obj_t *pObj = Aig_ManCo(solving_data.pAig, ith_co);
        const int var = PdrMultiTimeframe_ObjSatVar(p, solving_data, pObj, 0);
        int Lit = toLitCond(var, 1);
        int ret = sat_solver_addclause(pSat, &Lit, (&Lit)+1);
        assert(ret);
        (void)ret;
    }
    sat_solver_compress(pSat);
}

//////////////////////////////////////////////////////////////////////////
// Get solving data
//////////////////////////////////////////////////////////////////////////

static SolvingData PdrMultiTimeframe_ManGetSolvingData(Pdr_Man_t *p, Pdr_Obl_t *pThis, int timeframe_expansion) {
    if (timeframe_expansion > multiTimeframe::L) {
        timeframe_expansion = multiTimeframe::L;
    }

    if (multiTimeframe::pSat == nullptr) {
        multiTimeframe::pSat = zsat_solver_new_seed(p->pPars->nRandomSeed);
    }
    sat_solver *pSat = multiTimeframe::pSat;
    zsat_solver_restart_seed(pSat, p->pPars->nRandomSeed);
    Aig_Man_t* pAig = get_pAig(p, timeframe_expansion);
    Cnf_Dat_t* pCnf = multiTimeframe::pCnf_vec[timeframe_expansion];

    SolvingData solving_data(pSat, pAig, pCnf, pThis->iFrame, timeframe_expansion);
    PdrMultiTimeframe_ManSetPropertyOutput(p, solving_data);

    int i, j;
    Vec_Ptr_t *vArrayK;
    Pdr_Set_t *pCube;

    Vec_VecForEachLevelStart(p->vClauses, vArrayK, i, pThis->iFrame - timeframe_expansion) {
        Vec_PtrForEachEntry(Pdr_Set_t*, vArrayK, pCube, j) {
            for (int f = pThis->iFrame - timeframe_expansion; f < pThis->iFrame; ++f) {
                if (f <= i) {
                    Vec_Int_t *vLits = PdrMultiTimeframe_ManCubeToLits_at_frame(p, solving_data, pCube, 1, f);
                    int RetValue = sat_solver_addclause(solving_data.pSat, Vec_IntArray(vLits), 
                                                        Vec_IntArray(vLits) + Vec_IntSize(vLits));
                    assert(RetValue == 1);
                    (void)RetValue;
                    sat_solver_compress(solving_data.pSat);
                } else {
                    break;
                }
            }
        }
    }

    return solving_data;
}

//////////////////////////////////////////////////////////////////////////
// Block cube for first level (multi-timeframe)
//////////////////////////////////////////////////////////////////////////

static int PdrMultiTimeframe_ManBlockCube_for_first_level(Pdr_Man_t *p, Pdr_Obl_t *pThis, 
                                                          int timeframe_expansion, int& Prio) {
    if (!multiTimeframe::initialized) {
        PdrMultiTimeframe_init(p);
    }
    assert(timeframe_expansion > 1);

    Pdr_Set_t *pCubeMin = NULL;
    Pdr_Set_t *pPred = NULL;
    const int kMax = Vec_PtrSize(p->vSolvers)-1;
    assert(pThis->iFrame == kMax);

    SolvingData solving_data = PdrMultiTimeframe_ManGetSolvingData(p, pThis, timeframe_expansion);

    int i, k, RetValue;

    const abctime start_time = Abc_Clock();
    RetValue = PdrMultiTimeframe_ManGeneralize(p, pThis->pState, solving_data, &pPred, &pCubeMin);
    Pdr_AddSolvingTime(pThis->pState, Abc_Clock() - start_time);

    if (RetValue == -1) {
        Pdr_OblDeref(pThis);
        return -1;
    }
    
    if (RetValue) {
        assert(pCubeMin != NULL);
        assert(pPred == NULL);

        Pdr_Set_t* unsat_core_l_1 = NULL;
        const int refined = PdrMultiTimeframe_ManRecRefine(
            p, pThis->pState, solving_data.timeframe_expansion - 1, &unsat_core_l_1, false);
        if (refined == -1) {
            Pdr_SetDeref(pCubeMin);
            Pdr_OblDeref(pThis);
            return -1;
        }
        if (refined == 0) {
            return 0;
        }
        
        Pdr_Set_t* pCubeMin_temp = PdrMultiTimeframe_ManGet_blocking_cube(p, pCubeMin, unsat_core_l_1);
        Pdr_SetDeref(unsat_core_l_1);
        Pdr_SetDeref(pCubeMin);
        pCubeMin = pCubeMin_temp;

        k = pThis->iFrame;
        
        for (i = 0; i < pCubeMin->nLits; i++) {
            assert(pCubeMin->Lits[i] >= 0);
            assert((pCubeMin->Lits[i] / 2) < Aig_ManRegNum(p->pAig));
            if ((Vec_IntEntry(p->vPrio, pCubeMin->Lits[i] / 2) >> p->nPrioShift) == 0)
                p->nAbsFlops++;
            Vec_IntAddToEntry(p->vPrio, pCubeMin->Lits[i] / 2, 1 << p->nPrioShift);
        }
        
        for (i = 1; i <= k; i++) {
            Vec_VecPush(p->vClauses, i, pCubeMin);
            Pdr_SetRef(pCubeMin);
        }
        Pdr_SetDeref(pCubeMin);

        p->nCubes++;
        for (i = 1; i <= k; i++)
            Pdr_ManSolverAddClause(p, i, pCubeMin);

        Pdr_ProofObligationTree_RemoveProofObligation(pThis);
        Pdr_OblDeref(pThis);
    } else {
        assert(pCubeMin == NULL);
        assert(pPred != NULL);

        // child spans timeframe_expansion frames, not 1
        Pdr_ProofObligationTree_AddChild(pThis->pState, pPred, solving_data.timeframe_expansion);

        pThis->prio = Prio--;
        Pdr_QueuePush(p, pThis);
        pThis = Pdr_OblStart(pThis->iFrame - solving_data.timeframe_expansion, Prio--, pPred, Pdr_OblRef(pThis));
        Pdr_QueuePush(p, pThis);
    }

    if (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId))
        return -1;
    if (p->timeToStop && Abc_Clock() > p->timeToStop)
        return -1;
    if (p->timeToStopOne && Abc_Clock() > p->timeToStopOne)
        return -1;
    if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved && 
        Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
        return -1;
    return 1;
}

//////////////////////////////////////////////////////////////////////////
// Main multi-timeframe block cube function
//////////////////////////////////////////////////////////////////////////

// last effective fixed expansion announced in the log (fixed mode only)
static int mtf_fixed_last_printed_expansion = -1;

extern "C" int PdrMultiTimeframe_ManBlockCube(Pdr_Man_t *p, Pdr_Set_t *pCube) {
    Pdr_Obl_t *pThis;
    Pdr_Set_t *pPred, *pCubeMin;
    int i, k, RetValue, Prio = ABC_INFINITY, Counter = 0;
    int kMax = Vec_PtrSize(p->vSolvers)-1;
    abctime clk;
    abctime block_cube_start_clk = Abc_Clock();
    
    multi_timeframe_manager.init(block_cube_start_clk, pCube, kMax);
    // Alg. 3's l for this episode: 1 = standard PDR, > 1 = every top-level
    // pop blocks multi-frame at this depth. Only is_time_to_restart (dynamic
    // mode) or the -E block below ever raises it; nothing resets it to 1
    // within the episode.
    int timeframe_expansion_for_first_level = 1;

    // Fixed expansion mode (-E): every first-level query uses a
    // min(kMax, fixed) unrolling from the start; no trigger conditions.
    // kMax <= 1 falls back to the plain 1-frame query (expansion 1 is
    // identical to it, and downstream asserts expansion > 1)
    if (mtf_fixed_timeframe_expansion > 0) {
        int fixed_exp = min(kMax, min(mtf_fixed_timeframe_expansion, multiTimeframe::L));
        if (fixed_exp > 1) {
            timeframe_expansion_for_first_level = fixed_exp;
            if (fixed_exp != mtf_fixed_last_printed_expansion) {
                Abc_Print(1, "\nfixed timeframe_expansion: %d\n", fixed_exp);
                mtf_fixed_last_printed_expansion = fixed_exp;
            }
        }
    }

    p->nBlocks++;
    pThis = Pdr_OblStart(kMax, Prio--, pCube, NULL);
    Pdr_QueuePush(p, pThis);

    Pdr_ProofObligationTree_AddRootNode(pCube, pThis->iFrame, 0, 1);

    while (!Pdr_QueueIsEmpty(p)) {
        Counter++;
        pThis = Pdr_QueueHead(p);
        
        if (pThis->iFrame == 0 || (p->pPars->fUseAbs && Pdr_SetIsInit(pThis->pState, -1)))
            return 0;
        if (pThis->iFrame > kMax)
            return 1;
        if (p->nQueLim && p->nQueCur >= p->nQueLim) {
            p->nQueLim = p->nQueLim * 3 / 2;
            Pdr_QueueStop(p);
            return 1;
        }

        // Check if time to restart with multi-timeframe
        if (multi_timeframe_manager.is_time_to_restart(Abc_Clock(), timeframe_expansion_for_first_level)) {
            assert(timeframe_expansion_for_first_level > 1);
            if (timeframe_expansion_for_first_level > kMax) {
                timeframe_expansion_for_first_level = kMax;
            }
            assert(timeframe_expansion_for_first_level <= kMax);
            assert(timeframe_expansion_for_first_level <= multiTimeframe::L);

            block_cube_start_clk = Abc_Clock();
            // restart() cleans the queue; Pdr_QueueClean closes out the whole logger
            // tree (child-to-parent) and prints every root with is_restart: true
            multi_timeframe_manager.restart(block_cube_start_clk, p);
            assert(Pdr_ProofObligationTree_LevelFinishedCheck());
            Prio = ABC_INFINITY;
            pCube = multi_timeframe_manager.pCube;
            Pdr_SetRef(pCube);
            pThis = Pdr_OblStart(kMax, Prio--, pCube, NULL);
            Pdr_QueuePush(p, pThis);
            Pdr_ProofObligationTree_AddRootNode(pCube, pThis->iFrame, 0, 1);
            continue;
        }

        pThis = Pdr_QueuePop(p);
        assert(pThis->iFrame > 0);
        assert(!Pdr_SetIsInit(pThis->pState, -1));

        p->iUseFrame = Abc_MinInt(p->iUseFrame, pThis->iFrame);
        clk = Abc_Clock();
        
        if (Pdr_ManCheckContainment(p, pThis->iFrame, pThis->pState)) {
            p->tContain += Abc_Clock() - clk;
            Pdr_ProofObligationTree_RemoveProofObligation(pThis);
            Pdr_OblDeref(pThis);
            continue;
        }
        p->tContain += Abc_Clock() - clk;

        RetValue = Pdr_ManCheckCubeCs(p, pThis->iFrame, pThis->pState);
        if (RetValue == -1) {
            Pdr_OblDeref(pThis);
            return -1;
        }
        if (RetValue) {
            Pdr_ProofObligationTree_RemoveProofObligation(pThis);
            Pdr_OblDeref(pThis);
            continue;
        }

        // Use multi-timeframe for first level once escalated (l > 1)
        if (use_multi_timeframe && pThis->iFrame == kMax && timeframe_expansion_for_first_level > 1) {
            RetValue = PdrMultiTimeframe_ManBlockCube_for_first_level(p, pThis, timeframe_expansion_for_first_level, Prio);
            if (RetValue == 0) {
                return 0;
            }
            if (RetValue == -1) {
                return -1;
            }
            continue;
        }

        // Standard PDR generalization
        pCubeMin = NULL;
        const abctime generalize_start_time = Abc_Clock();
        RetValue = Pdr_ManGeneralize(p, pThis->iFrame-1, pThis->pState, &pPred, &pCubeMin);
        Pdr_AddSolvingTime(pThis->pState, Abc_Clock() - generalize_start_time);

        if (RetValue == -1) {
            Pdr_OblDeref(pThis);
            return -1;
        }
        
        if (RetValue) {
            assert(pCubeMin != NULL);
            k = pThis->iFrame;
            assert(pPred == NULL);
            
            for (k = pThis->iFrame; k < kMax; k++) {
                RetValue = Pdr_ManCheckCube(p, k, pCubeMin, NULL, 0, 0, 1);
                if (RetValue == -1) {
                    Pdr_OblDeref(pThis);
                    return -1;
                }
                if (!RetValue)
                    break;
            }
            
            for (i = 0; i < pCubeMin->nLits; i++) {
                assert(pCubeMin->Lits[i] >= 0);
                assert((pCubeMin->Lits[i] / 2) < Aig_ManRegNum(p->pAig));
                if ((Vec_IntEntry(p->vPrio, pCubeMin->Lits[i] / 2) >> p->nPrioShift) == 0)
                    p->nAbsFlops++;
                Vec_IntAddToEntry(p->vPrio, pCubeMin->Lits[i] / 2, 1 << p->nPrioShift);
            }
            Vec_VecPush(p->vClauses, k, pCubeMin);
            p->nCubes++;
            
            for (i = 1; i <= k; i++)
                Pdr_ManSolverAddClause(p, i, pCubeMin);

            Pdr_ProofObligationTree_RemoveProofObligation(pThis);

            // Schedule promoted root
            if ((k < kMax || p->pPars->fReuseProofOblig) && !p->pPars->fShortest) {
                pThis->iFrame = k+1;
                pThis->prio = Prio--;
                Pdr_QueuePush(p, pThis);
                Pdr_ProofObligationTree_AddRootNode(pThis->pState, pThis->iFrame, 1, pThis->pNext == NULL);
            } else {
                Pdr_OblDeref(pThis);
            }
        } else {
            assert(pCubeMin == NULL);
            assert(pPred != NULL);

            Pdr_ProofObligationTree_AddChild(pThis->pState, pPred, 1);

            pThis->prio = Prio--;
            Pdr_QueuePush(p, pThis);
            pThis = Pdr_OblStart(pThis->iFrame-1, Prio--, pPred, Pdr_OblRef(pThis));
            Pdr_QueuePush(p, pThis);
        }

        if (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId))
            return -1;
        if (p->timeToStop && Abc_Clock() > p->timeToStop)
            return -1;
        if (p->timeToStopOne && Abc_Clock() > p->timeToStopOne)
            return -1;
        if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved && 
            Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
            return -1;
    }

    assert(Pdr_ProofObligationTree_LevelFinishedCheck());
    double solving_time_for_block_cube = abctime_to_seconds(Abc_Clock() - block_cube_start_clk);
    multi_timeframe_manager.add_solving_time(solving_time_for_block_cube);
    multi_timeframe_manager.reset();
    return 1;
}

//////////////////////////////////////////////////////////////////////////
// Multi-timeframe CEX derivation
//////////////////////////////////////////////////////////////////////////

extern "C" Abc_Cex_t * PdrMultiTimeframe_ManDeriveCex(Pdr_Man_t *p, Pdr_Obl_t *pOblStart) {
    Abc_Cex_t *pCex;
    Pdr_Obl_t *pObl;
    int i, f, Lit, nFrames = 0;
    int total_obligations = 0;
    
    // count the number of frames
    for (pObl = pOblStart; pObl; pObl = pObl->pNext) {
        total_obligations++;
        int last_Pi_lit = pObl->pState->Lits[pObl->pState->nTotal - 1];
        const int nFrames_in_obl = (last_Pi_lit >= 0) ? 1 : -last_Pi_lit; // 4/12: if it's the last obligation, then nFrames_in_obl is 1
        nFrames += nFrames_in_obl;
    }

    // create the counter-example
    pCex = Abc_CexAlloc(Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), nFrames);
    pCex->iPo = p->iOutCur;
    pCex->iFrame = nFrames - 1;
    for (pObl = pOblStart, f = 0; pObl; pObl = pObl->pNext) {
        int last_Pi_lit = pObl->pState->Lits[pObl->pState->nTotal - 1];
        const int lit_end = (last_Pi_lit >= 0) ? pObl->pState->nTotal : pObl->pState->nTotal - 1; // 4/12: last number is BMC_length
        for (i = pObl->pState->nLits; i < lit_end; i++) {
            Lit = pObl->pState->Lits[i];
            if (Abc_LitIsCompl(Lit))
                continue;
            Abc_InfoSetBit(pCex->pData, pCex->nRegs + f * pCex->nPis + Abc_Lit2Var(Lit));
        }
        const int nFrames_in_obl = (last_Pi_lit >= 0) ? 1 : -last_Pi_lit; // 4/12: if it's the last obligation, then nFrames_in_obl is 1
        f += nFrames_in_obl;
    }
    assert(f == nFrames);
    if (!Saig_ManVerifyCex(p->pAig, pCex))
        Abc_Print(1, "PDR Multi-TF: CEX for output %d is not valid.\n", p->iOutCur);
    else {
        Abc_Print(1, "PDR Multi-TF: CEX for output %d is valid.\n", p->iOutCur);
    }
    
    return pCex;
}

#ifndef PDR_MULTI_TIMEFRAME_H
#define PDR_MULTI_TIMEFRAME_H

#include "proof/pdr/pdrInt.h"

#ifdef __cplusplus
extern "C" {
#endif

// Global flag to enable/disable multi-timeframe PDR (pdr -s; default off)
extern int use_multi_timeframe;

// Per-run reset: restart controller state and unrolled AIG/CNF/solver caches
// (must be called at the start of every PDR run when mt is enabled)
void PdrMultiTimeframe_OnRunStart(void);

// Multi-timeframe block cube function
// Returns: 0 = SAT (CEX found), 1 = UNSAT (cube blocked), -1 = resource limit
int PdrMultiTimeframe_ManBlockCube(Pdr_Man_t* p, Pdr_Set_t* pCube);

// Multi-timeframe CEX derivation function
// Handles the special format where last literal can be negative (timeframe expansion)
Abc_Cex_t* PdrMultiTimeframe_ManDeriveCex(Pdr_Man_t* p, Pdr_Obl_t* pOblStart);

#ifdef __cplusplus
}
#endif

#endif // PDR_MULTI_TIMEFRAME_H

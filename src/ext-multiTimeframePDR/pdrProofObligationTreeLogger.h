#ifndef PDR_PROOF_OBLIGATION_TREE_LOGGER_H
#define PDR_PROOF_OBLIGATION_TREE_LOGGER_H

#include "proof/pdr/pdrInt.h"

#ifdef __cplusplus
extern "C" {
#endif

// Runtime switch set by the "pdr" command (-l); all functions below are no-ops when 0
extern int use_proof_obligation_tree_logging;

// C-compatible function declarations
void Pdr_ProofObligationTree_AddRootNode(Pdr_Set_t* cube, int level, int is_promoted_root, int is_real_root);
void Pdr_AddSolvingTime(Pdr_Set_t *cube, abctime abc_time);
void Pdr_ProofObligationTree_AddChild(Pdr_Set_t* parent_cube, Pdr_Set_t* child_cube, int timeframe);
void Pdr_ProofObligationTree_RemoveProofObligation(Pdr_Obl_t *pThis);
// Close out and print every root (is_restart: true); call whenever the queue is discarded mid-search
void Pdr_ProofObligationTree_FlushAllRoots(void);
// Silently drop the whole tree (end of run; no records printed)
void Pdr_ProofObligationTree_Clear(void);
int Pdr_ProofObligationTree_LevelFinishedCheck(void);

#ifdef __cplusplus
}
#endif

#endif // PDR_PROOF_OBLIGATION_TREE_LOGGER_H

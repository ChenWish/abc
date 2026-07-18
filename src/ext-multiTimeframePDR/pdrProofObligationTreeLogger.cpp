#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "proof/pdr/pdrInt.h"
#include "ProofObligationTreeManager.h"
#include "StatisticsCollector.h"
#include "pdrProofObligationTreeLogger.h"

#include <cstdio>

ProofObligationTreeManager proof_obligation_tree_manager;

static void print_root_record(bool is_real_root, bool is_restart, int frame, const SubTreeInfo& sub_tree_info) {
    assert(!sub_tree_info.end_level_statistics_collector.is_empty());
    const int percentile_50_end_level = sub_tree_info.end_level_statistics_collector.get_percentile(0.5);
    const int min_end_level = sub_tree_info.end_level_statistics_collector.get_min();

    const int median_depth = frame - percentile_50_end_level;
    const int max_depth = frame - min_end_level;

    printf("\n");
    printf("*****\n");
    printf("%s\n", is_real_root ? "real root" : "promoted root");
    printf("is_restart: %s\n", is_restart ? "true" : "false");
    printf("frame: %d\n", frame);
    printf("median_depth: %d\n", median_depth);
    printf("max_depth: %d\n", max_depth);
    printf("percentile_50_end_level: %d\n", percentile_50_end_level);
    printf("min_end_level: %d\n", min_end_level);
    printf("intermediate_node_count: %d\n", sub_tree_info.intermediate_node_count);
    printf("leaf_node_count: %d\n", sub_tree_info.leaf_node_count);
    printf("solving_time: %.6f\n", sub_tree_info.solving_time);
    printf("*****\n");
    fflush(stdout);  // Ensure output is written immediately, even if process is killed
}

// C-compatible wrapper functions with extern "C" linkage
extern "C" {

int use_proof_obligation_tree_logging = 0;

void Pdr_ProofObligationTree_AddRootNode(Pdr_Set_t* cube, int level, int is_promoted_root, int is_real_root) {
    if (!use_proof_obligation_tree_logging)
        return;
    proof_obligation_tree_manager.add_root_node(cube, level, is_promoted_root != 0, is_real_root != 0);
}

void Pdr_AddSolvingTime(Pdr_Set_t *cube, abctime abc_time) {
    if (!use_proof_obligation_tree_logging)
        return;
    const double time_in_seconds = (1.0 * abc_time) / CLOCKS_PER_SEC;
    proof_obligation_tree_manager.add_solving_time(cube, time_in_seconds);
}

void Pdr_ProofObligationTree_AddChild(Pdr_Set_t* parent_cube, Pdr_Set_t* child_cube, int timeframe) {
    if (!use_proof_obligation_tree_logging)
        return;
    proof_obligation_tree_manager.add_child(parent_cube, child_cube, timeframe);
}

void Pdr_ProofObligationTree_RemoveProofObligation(Pdr_Obl_t *pThis) {
    if (!use_proof_obligation_tree_logging)
        return;
    const bool is_root = proof_obligation_tree_manager.fetch_node(pThis->pState)->is_root();
    SubTreeInfo sub_tree_info = proof_obligation_tree_manager.remove_node(pThis->pState);
    if (!is_root) {
        return;
    }

    const bool is_real_root = pThis->pNext == NULL;
    print_root_record(is_real_root, /*is_restart=*/false, pThis->iFrame, sub_tree_info);
}

void Pdr_ProofObligationTree_FlushAllRoots(void) {
    if (!use_proof_obligation_tree_logging)
        return;
    std::vector<ProofObligationTreeManager::RootFlushInfo> records =
        proof_obligation_tree_manager.flush_all_roots();
    for (const auto& record : records)
        print_root_record(record.is_real_root, /*is_restart=*/true, record.level, record.sub_tree_info);
}

void Pdr_ProofObligationTree_Clear(void) {
    proof_obligation_tree_manager.clear();
}

int Pdr_ProofObligationTree_LevelFinishedCheck() {
    if (!use_proof_obligation_tree_logging)
        return 1;
    return (proof_obligation_tree_manager.get_root_node_count() == 0 &&
            proof_obligation_tree_manager.get_node_count() == 0);
}

} // extern "C"

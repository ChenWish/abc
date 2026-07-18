#ifndef PROOF_OBLIGATION_TREE_MANAGER_H
#define PROOF_OBLIGATION_TREE_MANAGER_H

#include "base/abc/abc.h"
#include "proof/pdr/pdrInt.h"

#include "StatisticsCollector.h"

#include <vector>
#include <map>
#include <list>
#include <algorithm>
#include <cassert>
#include <memory>
#include <functional>

struct SubTreeInfo {
    int intermediate_node_count;
    int leaf_node_count;
    double solving_time;
    StatisticsCollector end_level_statistics_collector;

    double get_leaf_intermediate_ratio() const {
        if(intermediate_node_count == 0) {
            return 0.0;
        }
        return 1.0*leaf_node_count/intermediate_node_count;
    }

    SubTreeInfo() : intermediate_node_count(0), leaf_node_count(1), solving_time(0.0) {}
    SubTreeInfo(int level) : intermediate_node_count(0), leaf_node_count(1), solving_time(0.0) {}

    void initialized_by_child(const SubTreeInfo& child_sub_tree_info) {
        intermediate_node_count = child_sub_tree_info.intermediate_node_count + 1;
        leaf_node_count = child_sub_tree_info.leaf_node_count;
        solving_time += child_sub_tree_info.solving_time;
        const std::map<int, size_t>& child_frequency = child_sub_tree_info.end_level_statistics_collector.get_frequency();
        for (const auto& [level, count] : child_frequency) {
            end_level_statistics_collector.add(level);
        }
    }

    void updated_by_child(const SubTreeInfo& child_sub_tree_info) {
        intermediate_node_count += child_sub_tree_info.intermediate_node_count;
        leaf_node_count += child_sub_tree_info.leaf_node_count;
        solving_time += child_sub_tree_info.solving_time;
        const std::map<int, size_t>& child_frequency = child_sub_tree_info.end_level_statistics_collector.get_frequency();
        for (const auto& [level, count] : child_frequency) {
            end_level_statistics_collector.add(level);
        }
    }

    void add_end_level(int level) {
        end_level_statistics_collector.add(level);
    }
};

// Node class to represent a proof obligation node
class Node {
    friend class NodeManager;
    friend class ProofObligationTreeManager;

private:

    Pdr_Set_t* cube;
    Node* parent;  // Added parent pointer
    std::vector<Node*> children;
    int level;     // Added level member (iFrame)
    int depth;     // Added depth member
    bool is_promoted_root;  // true if this node is a promoted root
    bool is_real_root;      // true if the obligation has no parent obligation (pNext == NULL)
    bool is_leaf;   // Added leaf indicator
    SubTreeInfo sub_tree_info;

public:
    Node(Pdr_Set_t* cube_, int level_, int depth_, bool promoted_root = false, bool real_root = true) :
        cube(cube_),
        parent(nullptr),  // Initialize parent as nullptr
        level(level_),
        depth(depth_),
        is_promoted_root(promoted_root),
        is_real_root(real_root),
        is_leaf(true)    // Initialize as leaf
    {}

    // Accessor methods
    Pdr_Set_t* get_cube() const { return cube; }
    Node* get_parent() const { return parent; }
    const std::vector<Node*>& get_children() const { return children; }
    int get_level() const { return level; }
    int get_depth() const { return depth; }
    bool get_is_promoted_root() const { return is_promoted_root; }
    bool get_is_real_root() const { return is_real_root; }
    bool get_is_leaf() const { return is_leaf; }
    bool is_root() const { return parent == nullptr; }
    // Mutator methods
    void set_parent(Node* new_parent) { parent = new_parent; }
    void add_child(Node* child) {
        if (std::find(children.begin(), children.end(), child) != children.end()) {
            printf("Error: child already exists\n");
            assert(0);
        }
        children.push_back(child);
        child->set_parent(this);
        is_leaf = false;  // No longer a leaf when child is added
    }
    void set_depth(int new_depth) { depth = new_depth; }
    void set_level(int new_level) { level = new_level; }

    // Get root node by recursively traversing parents
    Node* get_root() const {
        const Node* current = this;
        while (current->parent != nullptr) {
            current = current->parent;
        }
        return const_cast<Node*>(current);
    }

    SubTreeInfo get_sub_tree_info() const {
        return sub_tree_info;
    }

    // called when a child node is removed
    void update_sub_tree_info(const SubTreeInfo& child_sub_tree_info) {
        if (sub_tree_info.intermediate_node_count == 0) {
            sub_tree_info.initialized_by_child(child_sub_tree_info);
        }
        else {
            sub_tree_info.updated_by_child(child_sub_tree_info);
        }
    }

    void add_end_level() {
        sub_tree_info.add_end_level(level);
    }

    void add_solving_time(double time) {
        sub_tree_info.solving_time += time;
    }
};

// NodeManager class to handle node creation and retrieval
class NodeManager {
private:
    std::map<Pdr_Set_t*, std::unique_ptr<Node>> nodes;

public:
    NodeManager() = default;
    
    // Prevent copying
    NodeManager(const NodeManager&) = delete;
    NodeManager& operator=(const NodeManager&) = delete;
    
    // Allow moving
    NodeManager(NodeManager&&) = default;
    NodeManager& operator=(NodeManager&&) = default;
    
    ~NodeManager() = default;  // unique_ptr handles cleanup automatically

    Node* add_node(Pdr_Set_t* cube, int level, int depth, bool promoted_root = false, bool real_root = true) {
        assert(!is_node_present(cube));
        auto new_node = std::make_unique<Node>(cube, level, depth, promoted_root, real_root);
        Node* node_ptr = new_node.get();
        nodes[cube] = std::move(new_node);
        return node_ptr;
    }

    Node* fetch_node(Pdr_Set_t* cube) const {
        auto it = nodes.find(cube);
        assert(it != nodes.end());
        return it->second.get();
    }

    void remove_node(Pdr_Set_t* cube) {
        auto it = nodes.find(cube);
        assert(it != nodes.end());
        nodes.erase(it);
    }

    bool is_node_present(Pdr_Set_t* cube) const {
        return nodes.find(cube) != nodes.end();
    }

    int get_node_count() const { return nodes.size(); }

    void clear() {
        nodes.clear();
    }
};

// ProofObligationTreeManager class to handle the tree structure
class ProofObligationTreeManager {
private:
    NodeManager node_manager;
    std::list<Node*> root_nodes;

    // Helper method for tree traversal
    void traverse_tree(Node* node, std::function<void(Node*)> visitor) const {
        if (!node) return;
        visitor(node);
        for (const Node* child : node->get_children()) {
            traverse_tree(const_cast<Node*>(child), visitor);
        }
    }

    // Remove all descendants of a node, children before parents, so each
    // removal merges its statistics into its parent via remove_node().
    void remove_descendants_postorder(Node* node) {
        while (!node->get_children().empty()) {
            Node* child = node->get_children().back();
            remove_descendants_postorder(child);
            remove_node(child->get_cube());
        }
    }

public:
    ProofObligationTreeManager() {}

    // Fetch a node by its cube
    Node* fetch_node(Pdr_Set_t* cube) const {
        if (!contains_node(cube)) {
            printf("Error: node not found in the tree\n");
            assert(0);
        }
        return node_manager.fetch_node(cube);
    }

    void add_child(Pdr_Set_t* parent_cube, Pdr_Set_t* child_cube, int timeframe = 1) {
        Node* parent = node_manager.fetch_node(parent_cube);
        assert(!node_manager.is_node_present(child_cube));
        Node* child = node_manager.add_node(child_cube, parent->get_level() - timeframe, parent->get_depth() + timeframe);
        parent->add_child(child);
    }

    void add_root_node(Pdr_Set_t* cube, int level, bool promoted_root = false, bool real_root = true) {
        Node* node = node_manager.add_node(cube, level, 0, promoted_root, real_root);
        root_nodes.push_back(node);
    }

    // returns the subtree info of the subtree rooted at the node
    SubTreeInfo remove_node(Pdr_Set_t* cube) {
        Node* node = node_manager.fetch_node(cube);
        if (node->get_is_leaf()) {
            node->add_end_level();
        }
        const SubTreeInfo sub_tree_info = node->get_sub_tree_info();
        if (node->parent) {
            auto& siblings = node->parent->children;
            auto it = std::find(siblings.begin(), siblings.end(), node);
            if(it != siblings.end()) {
                siblings.erase(it);
            }
            else {
                printf("node not found in parent's children list\n");
                assert(0);
            }
            node->parent->update_sub_tree_info(sub_tree_info);
        }
        else {
            // remove a root node
            // check if the node is a root nodd
            auto it = std::find(root_nodes.begin(), root_nodes.end(), node);
            if(it == root_nodes.end()) {
                printf("node not found in root_nodes despite having no parent\n");
                assert(0);
            }
            // check if the node has children
            if(!node->get_children().empty()) {
                printf("node has children, cannot be removed as root node\n");
                assert(0);
            }
            root_nodes.remove(node);
        }
        
        node_manager.remove_node(cube);
        return sub_tree_info;
    }

    void add_solving_time(Pdr_Set_t* cube, double time) {
        Node* node = node_manager.fetch_node(cube);
        node->add_solving_time(time);
    }

    // Get all nodes at a specific level
    std::vector<Node*> get_nodes_at_level(int target_level) {
        std::vector<Node*> result;
        for (Node* root : root_nodes) {
            traverse_tree(root, [&](Node* node) {
                if (node->get_level() == target_level) {
                    result.push_back(node);
                }
            });
        }
        return result;
    }

    // Get maximum depth of the tree
    int get_max_depth() const {
        int max_depth = 0;
        for (Node* root : root_nodes) {
            traverse_tree(root, [&](Node* node) {
                max_depth = std::max(max_depth, node->get_depth());
            });
        }
        return max_depth;
    }

    // Check if a node exists in the tree
    bool contains_node(Pdr_Set_t* cube) const {
        return node_manager.is_node_present(cube);
    }

    // Get all leaf nodes
    std::vector<Node*> get_leaf_nodes() {
        std::vector<Node*> leaves;
        for (Node* root : root_nodes) {
            traverse_tree(root, [&](Node* node) {
                if (node->get_children().empty()) {
                    leaves.push_back(node);
                }
            });
        }
        return leaves;
    }

    // Info of one root closed out by a restart flush
    struct RootFlushInfo {
        bool is_real_root;
        int level;
        SubTreeInfo sub_tree_info;
    };

    // Close out every root as if its whole subtree were removed normally:
    // descendants are removed post-order (child before parent), so end levels,
    // node counts and solving times accumulate upward by the same rules as
    // remove_node() in the regular flow. Returns one record per root.
    std::vector<RootFlushInfo> flush_all_roots() {
        std::vector<RootFlushInfo> records;
        while (!root_nodes.empty()) {
            Node* root = root_nodes.front();
            remove_descendants_postorder(root);
            RootFlushInfo record;
            record.is_real_root = root->get_is_real_root();
            record.level = root->get_level();
            record.sub_tree_info = remove_node(root->get_cube());
            records.push_back(record);
        }
        return records;
    }

    // Clear the entire tree
    void clear() {
        root_nodes.clear();
        node_manager.clear();
    }

    int get_root_node_count() const { return root_nodes.size(); }
    int get_node_count() const { return node_manager.get_node_count(); }
};

#endif // PROOF_OBLIGATION_TREE_MANAGER_H

package fr.uga.pddl4j.planners.liftedtreepath_smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;

public class PrimitiveTree {

    ArrayList<LiftedFlow> nodes;
    HashSet<Integer> rootNodesIdx;
    ArrayList<HashSet<Integer>> parentsNodesIdx;
    ArrayList<HashSet<Integer>> childrenNodesIdx;

    public PrimitiveTree() {
        this.nodes = new ArrayList<LiftedFlow>();
        this.parentsNodesIdx = new ArrayList<HashSet<Integer>>();
        this.childrenNodesIdx = new ArrayList<HashSet<Integer>>();
        this.rootNodesIdx = new HashSet<Integer>();
    }

    public void addNodeAndParentIfNotExist(LiftedFlow node, LiftedFlow parent) {
        if (!nodes.contains(node)) {
            nodes.add(node);
            parentsNodesIdx.add(new HashSet<>());
            childrenNodesIdx.add(new HashSet<>());
        }
        if (parent != null && !nodes.contains(parent)) {
            nodes.add(parent);
            parentsNodesIdx.add(new HashSet<>());
            childrenNodesIdx.add(new HashSet<>());
        }

        int idxNode = nodes.indexOf(node);

        if (parent != null) {
            int idxParentNode = nodes.indexOf(parent);

            if (rootNodesIdx.contains(idxNode)) {
                rootNodesIdx.remove(idxNode);
            }

            parentsNodesIdx.get(idxNode).add(idxParentNode);
            childrenNodesIdx.get(idxParentNode).add(idxNode);
        } else {
            rootNodesIdx.add(idxNode);
        }
    }

    public void addRootNode(LiftedFlow node) {
        if (!nodes.contains(node)) {
            nodes.add(node);
            parentsNodesIdx.add(new HashSet<>());
            childrenNodesIdx.add(new HashSet<>());

        }

        int idxNode = nodes.indexOf(node);
        this.rootNodesIdx.add(idxNode);
    }

    public void addNodeIfNotExist(LiftedFlow node, boolean isRoot) {
        if (!nodes.contains(node)) {
            nodes.add(node);
            parentsNodesIdx.add(new HashSet<>());
            childrenNodesIdx.add(new HashSet<>());
            if (isRoot) {
                int idxNode = nodes.indexOf(node);
                this.rootNodesIdx.add(idxNode);
            }
        }
    }

    public void addParentToNode(LiftedFlow node, LiftedFlow parent) {

        if (parent != null && !nodes.contains(parent)) {
            nodes.add(parent);
            parentsNodesIdx.add(new HashSet<>());
            childrenNodesIdx.add(new HashSet<>());
        }

        int idxNode = nodes.indexOf(node);

        int idxParentNode = nodes.indexOf(parent);

        if (rootNodesIdx.contains(idxNode)) {
            rootNodesIdx.remove(idxNode);
        }

        parentsNodesIdx.get(idxNode).add(idxParentNode);
        childrenNodesIdx.get(idxParentNode).add(idxNode);
    }

    public void clear() {
        this.nodes.clear();
        this.rootNodesIdx.clear();
        this.parentsNodesIdx.clear();
        this.childrenNodesIdx.clear();
    }

    public HashSet<LiftedFlow> getParents(LiftedFlow node) {
        // Get the idx of the node
        int idxNode = this.nodes.indexOf(node);
        HashSet<LiftedFlow> parentsNodes = new HashSet<LiftedFlow>(this.parentsNodesIdx.get(idxNode).size());
        for (int idxParentNode : this.parentsNodesIdx.get(idxNode)) {
            parentsNodes.add(this.nodes.get(idxParentNode));
        }

        return parentsNodes;
    }

    public HashSet<LiftedFlow> getChildren(LiftedFlow node) {
        HashSet<LiftedFlow> childrenNodes = new HashSet<LiftedFlow>();
        // Get the idx of the node
        int idxNode = this.nodes.indexOf(node);
        for (int idxChildNode : this.childrenNodesIdx.get(idxNode)) {
            childrenNodes.add(this.nodes.get(idxChildNode));
        }

        return childrenNodes;
    }

    public HashSet<LiftedFlow> getParents(Integer idxNode) {

        HashSet<LiftedFlow> parentsNodes = new HashSet<LiftedFlow>(this.parentsNodesIdx.get(idxNode).size());
        for (int idxParentNode : this.parentsNodesIdx.get(idxNode)) {
            parentsNodes.add(this.nodes.get(idxParentNode));
        }

        return parentsNodes;
    }


    /**
     * Returns the topological sort of the directed graph represented by
     * parentsNodesIdx.
     *
     * @return the topological sort of the graph, represented as a stack.
     */
    public Stack<Integer> getTopologicalSort() {
        int n = this.parentsNodesIdx.size();
        int[] inDegree = new int[n];
        Map<Integer, ArrayList<Integer>> graph = new HashMap<>();
        for (int i = 0; i < n; i++) {
            for (int neighbor : this.parentsNodesIdx.get(i)) {
                // Increment in-degree of the neighbor
                inDegree[neighbor]++;
                // Add the edge from node 'i' to node 'neighbor'
                if (!graph.containsKey(i)) {
                    graph.put(i, new ArrayList<>());
                }
                graph.get(i).add(neighbor);
            }
        }

        Queue<Integer> queue = new LinkedList<>();
        for (int i = 0; i < n; i++) {
            // Add node with 0 in-degree to the queue
            if (inDegree[i] == 0) {
                queue.offer(i);
            }
        }

        Stack<Integer> result = new Stack<>();
        while (!queue.isEmpty()) {
            int node = queue.poll();
            result.push(node);
            for (int neighbor : graph.getOrDefault(node, new ArrayList<>())) {
                inDegree[neighbor]--;
                if (inDegree[neighbor] == 0) {
                    queue.offer(neighbor);
                }
            }
        }
        return result;
    }
}

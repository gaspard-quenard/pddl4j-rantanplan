package fr.uga.pddl4j.planners.treerex_smt;

import java.util.List;
import java.util.Vector;
import java.util.function.Predicate;

import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;
import fr.uga.pddl4j.problem.operator.Method;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;

/**
 * An element of a tree rex layer
 */
public class LayerElement {

    private int maximumAmountSubsequentPositions;
    private int positionToPropagateInNextLayer;

    private int parentPosition;

    private boolean containsBlankAction;

    private Vector<Action> actions;
    private Vector<Method> reductions;
    private Vector<Fluent> positiveFluent;
    private Vector<Fluent> negativeFluent;

    private Vector<List<Integer>> cliques;
    private Vector<Integer> cliquesIdxLayer;
    private Vector<Integer> cliquesIdxPosition;

    public LayerElement(int _parentPosition) {
        this.actions = new Vector<Action>();
        this.reductions = new Vector<Method>();
        this.positiveFluent = new Vector<Fluent>();
        this.negativeFluent = new Vector<Fluent>();
        this.cliques = new Vector<List<Integer>>();
        this.cliquesIdxLayer = new Vector<Integer>();
        this.cliquesIdxPosition = new Vector<Integer>();
        // this.negativeCliques = new Vector<List<Integer>>();
        this.containsBlankAction = false;

        this.parentPosition = _parentPosition;
    }

    public void addReduction(Method reduction) {
        if (!this.reductions.contains(reduction)) {
            this.reductions.add(reduction);
        }
    }

    public void addAction(Action action) {
        if (!this.actions.contains(action)) {
            this.actions.add(action);
        }
    }

    public void addPositiveFluent(Fluent fluent) {
        if (!this.positiveFluent.contains(fluent)) {
            this.positiveFluent.add(fluent);
        }
    }

    public void addNegativeFluent(Fluent fluent) {
        if (!this.negativeFluent.contains(fluent)) {
        this.negativeFluent.add(fluent);
        }
    }

    public void addClique(List<Integer> clique, int layerIdx, int layerPosition) {
        if (!this.cliques.contains(clique)) {
            this.cliques.add(clique);
            this.cliquesIdxLayer.add(layerIdx);
            this.cliquesIdxPosition.add(layerPosition);
        }
    }

    // public void addNegativeFluentClique(List<Integer> clique) {
    //     if (!this.negativeCliques.contains(clique)) {
    //     this.negativeCliques.add(clique);
    //     }
    // }


    public void addBlankAction() {
        this.containsBlankAction = true;
    }

    public Vector<Action> getActions() {
        return this.actions;
    }

    public boolean canContainsBlankAction() {
        return this.containsBlankAction;
    }

    public Vector<Method> getReductions() {
        return this.reductions;
    }

    public Vector<Fluent> getPositivesFluents() {
        return this.positiveFluent;
    }


    public Vector<Fluent> getNegativesFluents() {
        return this.negativeFluent;
    }


    public Vector<List<Integer>> getFluentCliques() {
        return this.cliques;
    }

    public Vector<Integer> getFluentCliquesLayerIdx() {
        return this.cliquesIdxLayer;
    }

    public Vector<Integer> getFluentCliqueLayerPosition() {
        return this.cliquesIdxPosition;
    }


    // public Vector<List<Integer>> getNegativesFluentCliques() {
    //     return this.negativeCliques;
    // }

    public int computeNumberChildren() {

        // There is at least one children.
        int numberChildren = 1;
        // Now, let's see the maximum decomposition of all the reductions
        for (Method method : this.reductions) {
            int numberSubstasks = method.getSubTasks().size();
            if (numberSubstasks > numberChildren) {
                numberChildren = numberSubstasks;
            }
        }

        return numberChildren;
    }

    /**
     * Return the position of the layerElement in the previous layer which has created this layerElement
     * @return
     */
    public int getParentPosition() {
        return this.parentPosition;
    }
}

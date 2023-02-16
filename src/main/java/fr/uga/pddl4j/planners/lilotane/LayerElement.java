package fr.uga.pddl4j.planners.lilotane;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
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

    private int parentPosition;

    private boolean containsBlankAction;

    private Vector<Action> actions;
    private Vector<Method> reductions;
    private Vector<Fluent> positiveFluent;
    private Vector<Fluent> negativeFluent;
    
    private Map<String, ArrayList<ScopeVariable>> liftedReductionsWithScope;
    // An action scope heritate from a method. So we can indicate for each argument of the action, the argument of the method it heritate
    private Map<String, ArrayList<ScopeVariable>> liftedActionsWithScope;

    private HashSet<LiftedMethod> liftedReductions;
    private HashSet<LiftedAction> liftedActions;
    private HashSet<PseudoFact> pseudoFacts;

    private Vector<List<Integer>> cliques;
    private Vector<Integer> cliquesIdxLayer;
    private Vector<Integer> cliquesIdxPosition;

    public LayerElement(int _parentPosition) {
        this.actions = new Vector<Action>();
        this.reductions = new Vector<Method>();
        this.liftedReductionsWithScope = new HashMap<String, ArrayList<ScopeVariable>>();
        this.liftedActionsWithScope = new HashMap<>();
        this.positiveFluent = new Vector<Fluent>();
        this.negativeFluent = new Vector<Fluent>();
        this.cliques = new Vector<List<Integer>>();
        this.cliquesIdxLayer = new Vector<Integer>();
        this.cliquesIdxPosition = new Vector<Integer>();
        this.pseudoFacts = new HashSet<PseudoFact>();
        this.liftedReductions = new HashSet<LiftedMethod>();
        this.liftedActions = new HashSet<LiftedAction>();
        // this.negativeCliques = new Vector<List<Integer>>();
        this.containsBlankAction = false;

        this.parentPosition = _parentPosition;
    }

    public void addReduction(Method reduction) {
        if (!this.reductions.contains(reduction)) {
            this.reductions.add(reduction);
        }
    }

    public void addLiftedReduction(LiftedMethod liftedReduction) {
        if (!this.liftedReductions.contains(liftedReduction)) {
            this.liftedReductions.add(liftedReduction);
        }
    }

    public void addLiftedAction(LiftedAction liftedAction) {
        if (!this.liftedActions.contains(liftedAction)) {
            this.liftedActions.add(liftedAction);
        }
    }

    public HashSet<LiftedMethod> getLiftedReductions() {
        return this.liftedReductions;
    }

    public HashSet<LiftedAction> getLiftedActions() {
        return this.liftedActions;
    }

    public void addLiftedReductionWithScope(String methodName, ArrayList<ScopeVariable> scopeParameters) {
        if (!this.liftedReductionsWithScope.containsKey(methodName)) {
            this.liftedReductionsWithScope.put(methodName, scopeParameters);
        } else {
            // Update scope here ?
            this.liftedReductionsWithScope.put(methodName, scopeParameters);
        }
    }

    public void addLiftedActionWithScope(String actionName, ArrayList<ScopeVariable> scopeParameters) {
        if (!this.liftedActionsWithScope.containsKey(actionName)) {
            this.liftedActionsWithScope.put(actionName, scopeParameters);
        } else {
            // Update scope here ?
            this.liftedActionsWithScope.put(actionName, scopeParameters);
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

    // public void addNegativeFluent(Fluent fluent) {
    //     if (!this.negativeFluent.contains(fluent)) {
    //     this.negativeFluent.add(fluent);
    //     }
    // }

    // For now, positive fluent and negative fluent are treated in the same way
    public void addNegativeFluent(Fluent fluent) {
        if (!this.positiveFluent.contains(fluent)) {
        this.positiveFluent.add(fluent);
        }
    }

    public void addClique(List<Integer> clique, int layerIdx, int layerPosition) {
        if (!this.cliques.contains(clique)) {
            this.cliques.add(clique);
            this.cliquesIdxLayer.add(layerIdx);
            this.cliquesIdxPosition.add(layerPosition);
        }
    }

    public void addPseudoFact(PseudoFact pseudoFact) {
        this.pseudoFacts.add(pseudoFact);
    }

    public HashSet<PseudoFact> getPseudoFacts() {
        return this.pseudoFacts;
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

    public Map<String, ArrayList<ScopeVariable>> getLiftedReductionWithScope() {
        return this.liftedReductionsWithScope;
    }


    public Map<String, ArrayList<ScopeVariable>> getLiftedActionWithScope() {
        return this.liftedActionsWithScope;
    }

    public Vector<Fluent> getPositivesFluents() {
        return this.positiveFluent;
    }


    // public Vector<Fluent> getNegativesFluents() {
    //     return this.negativeFluent;
    // }

    // For now, positive fluent and negative fluent are treated in the same way
    public Vector<Fluent> getNegativesFluents() {
        return this.positiveFluent;
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

    public int computeNumberChildren(Map<String, Integer> liftedMethodNameToNumberSubtasks) {

        // There is at least one children.
        int numberChildren = 1;
        int numberSubtasks;
        // Now, let's see the maximum decomposition of all the reductions
        for (LiftedMethod liftedMethod: this.liftedReductions) {
            // Get a method with the same name as this method
            numberSubtasks = liftedMethodNameToNumberSubtasks.get(liftedMethod.getName());
            if (numberSubtasks > numberChildren) {
                numberChildren = numberSubtasks;
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

package fr.uga.pddl4j.planners.treerex_smt;

import java.util.Vector;

import javax.lang.model.element.Element;

import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Method;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import fr.uga.pddl4j.util.BitVector;

enum SAT_RESULT {
    UNSAT,
    SAT
}

public class TreeRexEncoder {

    private final Problem problem;

    private int actionsSize;
    private int factsSize;
    private String filenameSMTFile = "test.SMT";
    private Vector<Layer> layers = new Vector<Layer>();

    StringBuilder allClauses;
    Vector<String> allVariables;

    public TreeRexEncoder(Problem problem) {
        this.problem = problem;

        this.actionsSize = this.problem.getActions().size();
        this.factsSize = this.problem.getFluents().size();
        this.allVariables = new Vector<String>();
        this.allClauses = new StringBuilder();
    }

    /**
     * Return a string containing an action in easily readable format
     * 
     * @param a       The action to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the action in easily readable format
     */
    public String prettyDisplayAction(Action a, Problem problem) {
        StringBuilder actionToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        actionToDisplay.append("ACTION_" + a.getName());

        // Then, for each argument of this fluent, add the argument into the string
        for (int actionArg : a.getInstantiations()) {
            actionToDisplay.append("_" + problem.getConstantSymbols().get(actionArg));
        }

        return actionToDisplay.toString();
    }

    /**
     * Return a string containing a method in easily readable format
     * 
     * @param a       The method to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the action in easily readable format
     */
    private String prettyDisplayMethod(Method m, Problem problem) {
        StringBuilder methodToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        methodToDisplay.append("METHOD_" + m.getName());

        // Then, for each argument of this fluent, add the argument into the string
        for (int methodArg : m.getInstantiations()) {
            methodToDisplay.append("_" + problem.getConstantSymbols().get(methodArg));
        }

        return methodToDisplay.toString();
    }

    /**
     * Return a string containing a fluent in easily readable format
     * 
     * @param f       The fluent to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the fluent in easily readable format
     */
    private String prettyDisplayFluent(Fluent f, Problem problem) {
        StringBuilder fluentToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        fluentToDisplay.append("FLUENT_" + problem.getPredicateSymbols().get(f.getSymbol()));

        // Then, for each argument of this fluent, add the argument into the string
        for (int fluentArg : f.getArguments()) {
            fluentToDisplay.append("_" + problem.getConstantSymbols().get(fluentArg));
        }

        return fluentToDisplay.toString();
    }


    private String addLayerAndPos(String varToAdd, int layer, int pos) {
        return varToAdd + "__" + Integer.toString(layer) + "_" + Integer.toString(pos);
    }

    /**
     * # represent the layer and @ represention the position in the layer
     * 
     * @param fluentOrAction
     * @return
     */

    private String getBlankAction() {
        return "ACTION_Blank";
    }

    private String getPrimitivePredicate() {
        return "Primitive";
    }




    public String addInitialStateConstrains() {

        StringBuilder constrainsInitState = new StringBuilder();

        String var;

        // RULE 1 -> Inital facts hold at position 0
        constrainsInitState.append("; rule 1: Initals facts hold at pos 0\n");
        for (int i = 0; i < this.factsSize; i++) {
            Fluent f = this.problem.getFluents().get(i);
            var = addLayerAndPos(prettyDisplayFluent(f, problem), 0, 0);
            addToAllVariables(var);
            if (this.problem.getInitialState().getPositiveFluents().get(i)) {

                
                constrainsInitState
                        .append("(assert (= " +
                        var
                                + " true))\n");

                this.layers.get(0).layerElements.get(0).addPositiveFluent(f);
            } else {
                constrainsInitState
                        .append("(assert (= "
                                + var
                                + " false))\n");

                this.layers.get(0).layerElements.get(0).addNegativeFluent(f);
            }
        }

        constrainsInitState.append("; rule 2: Reduction initial task network\n");
        int number_elements_in_first_layer = this.problem.getInitialTaskNetwork().getTasks().size();
        // RULE 2 -> Get all reduction of the initial task networks. 

        Layer layer0 = this.layers.get(0);

        for (int i = 0; i < this.problem.getInitialTaskNetwork().getTasks().size(); i++) {
            LayerElement layerElm =layer0.layerElements.get(i);

            int idxTaskNetwork = this.problem.getInitialTaskNetwork().getTasks().get(i);

            constrainsInitState.append("(assert (or ");
            // Get all the methods which can solve this task
            for (int idxMethod = 0; idxMethod < this.problem.getMethods().size(); idxMethod++) {
                if (this.problem.getMethods().get(idxMethod).getTask() == idxTaskNetwork) {
                    Method m = this.problem.getMethods().get(idxMethod);
                    var = addLayerAndPos(prettyDisplayMethod(m, problem), 0, i);
                    constrainsInitState.append(var + " ");

                    addToAllVariables(var);

                    layerElm.addReduction(m);
                } 
            }
            constrainsInitState.append("))\n");
        }

        // Add the final layerElement which only contains the blank action
        LayerElement lastLayerElm = layer0.layerElements.lastElement();

        // RULE 3 -> Add a blank element to the last position of the initial layer
        constrainsInitState.append("; rule 3: Blank element at last position of init layer\n");
        var = addLayerAndPos(getBlankAction(), 0, number_elements_in_first_layer);
        addToAllVariables(var);
        constrainsInitState.append(
                "(assert (= " + var + " true))\n");

        lastLayerElm.addBlankAction();

        // RULE 4 -> All goal facts must hold in final element
        constrainsInitState.append("; rule 4: All facts hold at last position of init layer\n");
        for (int i = 0; i < this.factsSize; i++) {
            if (this.problem.getGoal().getPositiveFluents().get(i)) {
                Fluent f = this.problem.getFluents().get(i);
                var = addLayerAndPos(prettyDisplayFluent(f, problem), 0, number_elements_in_first_layer);
                addToAllVariables(var);
                constrainsInitState.append("(assert (= "
                        + var
                        + " true))\n");

                lastLayerElm.addPositiveFluent(f);
            }
        }

        return constrainsInitState.toString();
    }

    private String rule10(int layerIdx) {

        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();
        StringBuilder constrainsDescendants = new StringBuilder();
        constrainsDescendants.append("; rule 10: A fact also holds at its first child position\n");
        for (int layerElm = 0; layerElm < numberElementsInLayer; layerElm++) {
            int childLayerElm = this.layers.get(layerIdx).n.get(layerElm);
            for (int i = 0; i < this.factsSize; i++) {
                Fluent f = this.problem.getFluents().get(i);
                String varFluent = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx, layerElm);
                String varFluentInChildLayer = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx + 1, childLayerElm);
                addToAllVariables(varFluent);
                addToAllVariables(varFluentInChildLayer);
                constrainsDescendants.append("(assert (=> " + varFluent + " " + varFluentInChildLayer + "))\n");
                constrainsDescendants
                        .append("(assert (=> " + varFluentInChildLayer + " " + varFluent + "))\n");
            }
        }

        return constrainsDescendants.toString();
    }

    private String rule11(int layerIdx) {

        StringBuilder constrainsRule11 = new StringBuilder();

        constrainsRule11.append("; rule 11: Action occur implies it will occur at its first child position\n");
        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();
        for (int layerElm = 0; layerElm < numberElementsInLayer; layerElm++) {
            int childLayerElm = this.layers.get(layerIdx).n.get(layerElm);
            Vector<Action> availableActionForThisLayerAndPos = this.layers.get(layerIdx).layerElements.get(layerElm)
                    .getActions();

            // Since this action can happen to this position in the next layer, we
            // have to add it to the possible action occuring to the next position
            LayerElement layerElement = this.layers.get(layerIdx).layerElements.get(layerElm);
            LayerElement childLayerElement = this.layers.get(layerIdx + 1).layerElements.get(childLayerElm);

            for (Action a : availableActionForThisLayerAndPos) {
                String varAction = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx, layerElm);
                String varActionNextLayer = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx + 1, childLayerElm);
                addToAllVariables(varAction);
                addToAllVariables(varActionNextLayer);
                constrainsRule11.append("(assert (=> " + varAction + " " + varActionNextLayer + "))\n");
                childLayerElement.addAction(a);
            }

            // Add as well the blank action if this layer can have a blank action
            if (layerElement.canContainsBlankAction()) {
                String varBlankAction = addLayerAndPos(getBlankAction(), layerIdx, layerElm);
                String varBlankActionNextLayer = addLayerAndPos(getBlankAction(), layerIdx + 1, childLayerElm);
                addToAllVariables(varBlankAction);
                addToAllVariables(varBlankActionNextLayer);
                constrainsRule11.append("(assert (=> " + varBlankAction + " " + varBlankActionNextLayer + "))\n");
                childLayerElement.addBlankAction();
            }
        }

        return constrainsRule11.toString();
    }

    private String rule12(int layerIdx) {
        StringBuilder constrainsRule12 = new StringBuilder();
        constrainsRule12.append("; rule 12: If action occurs, all further child will contains blank action\n");
        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();

        for (int layerElm = 0; layerElm < numberElementsInLayer; layerElm++) {
            int nbChildElms = this.layers.get(layerIdx).e.get(layerElm);
            int firstPosChildElm = this.layers.get(layerIdx).n.get(layerElm);
            
            if (nbChildElms > 1) {
                for (Action a : this.layers.get(layerIdx).layerElements.get(layerElm).getActions()) {
                    String varAction = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx, layerElm);
                    addToAllVariables(varAction);
                    constrainsRule12
                            .append("(assert (=> " + varAction + " (and ");
                    for (int childIdx = 1; childIdx < nbChildElms; childIdx++) {
                        String varBlankAction = addLayerAndPos(getBlankAction(), layerIdx + 1, firstPosChildElm + childIdx);
                        addToAllVariables(varBlankAction);
                        constrainsRule12
                                .append(varBlankAction + " ");

                        // TODO Should add blank action to layer here ?
                        // this.layers.get(layerIdx + 1).layerElements.get(firstPosChildElm + childIdx).addBlankAction();
                    }
                    constrainsRule12.append(")))\n"); 
                }
            }

            // Do not forget to do the same things if a blank action occurs.
            // TODO I THINK THAT ALL ELEMENT COULD CONTAINS A BLANK ACTION
            // if
            // (this.layers.get(layerIdx).layerElements.get(layerElm).canContainsBlankAction())
            // {
            // constrainsRule12
            // .append("(assert (=> " + addLayerAndPos(getBlankAction(), layerElm, layerElm)
            // + " (and ");
            // for (int childIdx = 0; childIdx < nbChildElms; childIdx++) {
            // constrainsRule12
            // .append(addLayerAndPos(getBlankAction(), layerElm + 1, firstPosChildElm +
            // childIdx) + " ");
            // }
            // constrainsRule12.append("))\n");
            // }
        }
        return constrainsRule12.toString();
    }

    private String rule13_14_15(int layerIdx) {
        StringBuilder constrainsRule13_14_15 = new StringBuilder();
        constrainsRule13_14_15.append("; rule 13, 14, 15: Reduction to action, or to all subreduction of each subtasks\n");
        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();

        for (int layerElm = 0; layerElm < numberElementsInLayer; layerElm++) {
            int nbChildElms = this.layers.get(layerIdx).e.get(layerElm);
            int firstPosChildElm = this.layers.get(layerIdx).n.get(layerElm);
            // Get the methods available for this layer element
            Vector<Method> methodsAvailable = this.layers.get(layerIdx).layerElements.get(layerElm).getReductions();

            // For each method which can be exectuted in this layerElement
            for (Method m : methodsAvailable) {

                String varMethod = addLayerAndPos(prettyDisplayMethod(m, problem), layerIdx, layerElm);
                addToAllVariables(varMethod);

                // Get all subtask for the method
                for (int i_subtask = 0; i_subtask < m.getSubTasks().size(); i_subtask++) {

                    int subtask = m.getSubTasks().get(i_subtask);
                    LayerElement layerElement = this.layers.get(layerIdx + 1).layerElements
                    .get(firstPosChildElm + i_subtask);       

                    constrainsRule13_14_15.append(
                            "(assert (=> " + varMethod + " ");

                    // RULE 14 Reduction to actions
                    if (this.problem.getTasks().get(subtask).isPrimtive()) {
                        // Get the action which accomplish the method
                        Action a = this.problem.getActions().get(this.problem.getTaskResolvers().get(subtask).get(0));

                        String varActionNextLayer = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx + 1, firstPosChildElm + i_subtask);

                        constrainsRule13_14_15.append(varActionNextLayer + "))\n");

                        // Add the action as well to the Tree
                        layerElement.addAction(a);
                    }
                    // Else it means that one or multiple method can solve this subtask
                    // RULE 14 Reduction to methods
                    else {
                        constrainsRule13_14_15.append("(or ");
                        // Find the methods which can solve this subtask
                        for (int idxMethod = 0; idxMethod < this.problem.getMethods().size(); idxMethod++) {
                            if (this.problem.getMethods().get(idxMethod).getTask() == subtask) {
                                Method subMethod = this.problem.getMethods().get(idxMethod);
                                String varMethodNextLayer = addLayerAndPos(prettyDisplayMethod(subMethod, problem), layerIdx + 1, firstPosChildElm + i_subtask);
                                constrainsRule13_14_15.append(varMethodNextLayer + " ");

                                // Add as well this method is our Tree
                                layerElement.addReduction(subMethod);
                            }
                        }
                        constrainsRule13_14_15.append(")))\n");
                    }
                }

                // RULE 15 Reduction to blank actions
                for (int i = m.getSubTasks().size(); i < nbChildElms; i++) {
                    String varBlankAction = addLayerAndPos(getBlankAction(), layerIdx + 1, firstPosChildElm + i);
                    addToAllVariables(varBlankAction);
                    constrainsRule13_14_15.append("(assert (=> " + varMethod + " " + varBlankAction + "))\n");

                    // Add as well the blank action to our layer
                    this.layers.get(layerIdx + 1).layerElements.get(firstPosChildElm + i).addBlankAction();   
                }
            }
        }
        return constrainsRule13_14_15.toString();
    }

    private String rule16(int layerIdx) {
        StringBuilder constrainsRule16 = new StringBuilder();
        constrainsRule16.append("; All position of the current layer must be primitive\n");
        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();
        constrainsRule16.append("(assert (and ");
        for (int idxElmLayer = 0; idxElmLayer < numberElementsInLayer; idxElmLayer++) {
            String varPrimitivePredicate = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
            addToAllVariables(varPrimitivePredicate);
            constrainsRule16.append(varPrimitivePredicate + " ");
        }
        constrainsRule16.append("))\n");
        return constrainsRule16.toString();
    }

    private String addUniversalConstrains(int layerIdx) {

        StringBuilder universalConstrains = new StringBuilder();
        String var;

        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();

        universalConstrains.append("; universal constrains for layer " + layerIdx + "\n");

        for (int idxElmLayer = 0; idxElmLayer < numberElementsInLayer; idxElmLayer++) {
            universalConstrains.append("; For element " + idxElmLayer + "/" + (numberElementsInLayer - 1) + "\n");

            Vector<Action> availableActionForThisLayerAndPos = this.layers.get(layerIdx).layerElements.get(idxElmLayer).getActions();
            int nbAction = availableActionForThisLayerAndPos.size();

            // Rule 5
            // Get all actions available for this layer elements
            universalConstrains.append("; rule 5: action implies precond and effects\n");
            for (Action action : this.layers.get(layerIdx).layerElements.get(idxElmLayer).getActions()) {

                if (action.getPrecondition().getPositiveFluents().length() + action.getPrecondition().getNegativeFluents().length() == 0) {
                    continue;
                }
                String varAction = addLayerAndPos(prettyDisplayAction(action, problem), layerIdx, idxElmLayer);
                addToAllVariables(varAction);
                universalConstrains.append("(assert (=> "
                        + varAction + " (and ");

                // Get the preconditions of the action
                for (int i = 0; i < this.factsSize; i++) {
                    Fluent f = this.problem.getFluents().get(i);
                    if (action.getPrecondition().getPositiveFluents().get(i)) {
                        String fluentVar = prettyDisplayFluent(f, problem);
                        String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                        addToAllVariables(varFluent);
                        universalConstrains.append(varFluent + " ");
                    }
                    if (action.getPrecondition().getNegativeFluents().get(i)) {
                        String fluentVar = prettyDisplayFluent(f, problem);
                        String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                        addToAllVariables(varFluent);
                        universalConstrains
                                .append("( not " + varFluent + " ) ");
                    }
                }
                universalConstrains.append(")))\n");

                // Add the effects of the actions as well
                universalConstrains.append("(assert (=> "
                + varAction + " (and ");
                for (int i = 0; i < this.factsSize; i++) {
                    Boolean factInPositiveFluent = false;
                    Fluent f = this.problem.getFluents().get(i);
                    if (action.getUnconditionalEffect().getPositiveFluents().get(i)) {
                        String fluentVar = prettyDisplayFluent(f, problem);
                        String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer + 1);
                        addToAllVariables(varFluent);
                        universalConstrains.append(varFluent + " ");
                        factInPositiveFluent = true; // We have an incorect state if a fact is both a positive and negative fluent of an action (e.g: move f0 f0 -> lift at f0 and not lift at f0 for the next element)
                    }
                    if (action.getUnconditionalEffect().getNegativeFluents().get(i) && !factInPositiveFluent) {
                        String fluentVar = prettyDisplayFluent(f, problem);
                        String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer + 1);
                        addToAllVariables(varFluent);
                        universalConstrains
                                .append("( not " + varFluent + " ) ");
                    }
                }
                universalConstrains.append(")))\n");
            }

            // Rule 6
            universalConstrains.append("; rule 6: reduction implies preconditions\n");
            for (Method method : this.layers.get(layerIdx).layerElements.get(idxElmLayer).getReductions()) {

                var = addLayerAndPos(prettyDisplayMethod(method, problem), layerIdx, idxElmLayer);
                addToAllVariables(var);
                universalConstrains.append("(assert (=> "
                        + var + " (and true "); // True is used to have a correct file event if there is no preconditions

                // Get the positives preconditions of the action
                for (int i = 0; i < this.factsSize; i++) {
                    Fluent f = this.problem.getFluents().get(i);
                    if (method.getPrecondition().getPositiveFluents().get(i)) {
                        String fluentVar = prettyDisplayFluent(f, problem);
                        var = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                        addToAllVariables(var);
                        universalConstrains.append(var + " ");
                    }
                    if (method.getPrecondition().getNegativeFluents().get(i)) {
                        String fluentVar = prettyDisplayFluent(f, problem);
                        var = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                        addToAllVariables(var);
                        universalConstrains.append("(not " + var + ") ");
                    }
                }
                universalConstrains.append(")))\n");
            }

            // Rule 7
            universalConstrains.append("; rule 7: action is primitive, reduction is not primitive\n");
            for (Action action : this.layers.get(layerIdx).layerElements.get(idxElmLayer).getActions()) {
                String varAction = addLayerAndPos(prettyDisplayAction(action, problem), layerIdx, idxElmLayer);
                String varPrimitivePredicate = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
                addToAllVariables(varAction);
                addToAllVariables(varPrimitivePredicate);
                universalConstrains.append("(assert (=> "
                        + varAction + " ");
                universalConstrains.append(varPrimitivePredicate + "))\n");
            }
            for (Method method : this.layers.get(layerIdx).layerElements.get(idxElmLayer).getReductions()) {
                String varMethod = addLayerAndPos(prettyDisplayMethod(method, problem), layerIdx, idxElmLayer);
                String varPrimitivePredicate = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
                addToAllVariables(varMethod);
                addToAllVariables(varPrimitivePredicate);
                universalConstrains.append("(assert (=> " + varMethod + " ");
                universalConstrains
                        .append("(not " + varPrimitivePredicate + ")))\n");
            }
            if (this.layers.get(layerIdx).layerElements.get(idxElmLayer).canContainsBlankAction()) {
                String varBlankAction = addLayerAndPos(getBlankAction(), layerIdx, idxElmLayer);
                String varPrimitivePredicate = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
                addToAllVariables(varBlankAction);
                addToAllVariables(varPrimitivePredicate);
                universalConstrains.append("(assert (=> " + varBlankAction + " " + varPrimitivePredicate + "))\n");
            }
               

            // Rule 8
            universalConstrains.append("; rule 8: frame axioms\n");
            if (idxElmLayer < numberElementsInLayer - 1) 
            {
                for (int i = 0; i < this.factsSize; i++) {
                    Fluent f = this.problem.getFluents().get(i);
                    String varFluent = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx, idxElmLayer);
                    String varFluentNextElm = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx, idxElmLayer + 1);
                    String varPrimitivePred = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
                    addToAllVariables(varFluent);
                    addToAllVariables(varFluentNextElm);
        
                    universalConstrains.append("(assert (=> (and " + varFluent + " (not " + varFluentNextElm + ")) ");
        
                    universalConstrains.append("(or (not " + varPrimitivePred + ") ");
                    for (Action a : availableActionForThisLayerAndPos) {
                        if (a.getUnconditionalEffect().getNegativeFluents().get(i)) {
                            String varAction = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx, idxElmLayer);
                            addToAllVariables(varAction);
                            universalConstrains.append(varAction + " ");
                        }
                    }
                    universalConstrains.append(")))\n");
                    universalConstrains.append("(assert (=> (and (not " + varFluent + ") " + varFluentNextElm + ") ");
        
                            universalConstrains.append("(or (not " + varPrimitivePred + ") ");
                    for (Action a : availableActionForThisLayerAndPos) {
                        if (a.getUnconditionalEffect().getPositiveFluents().get(i)) {
                            String varAction = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx, idxElmLayer);
                            addToAllVariables(varAction);   
                            universalConstrains.append(varAction + " ");
                        }
                    }
                    universalConstrains.append(")))\n");
                }
            }
            

         
            // Rule 9
            universalConstrains.append("; rule 9: At most one action\n");
            for (int i = 0; i < nbAction; i++) {
                Action a1 = availableActionForThisLayerAndPos.get(i);
                String varAction1 = addLayerAndPos(prettyDisplayAction(a1, problem), layerIdx, idxElmLayer);
                addToAllVariables(varAction1);
                for (int j = i + 1; j < nbAction; j++) {
                    Action a2 = availableActionForThisLayerAndPos.get(j);
                    String varAction2 = addLayerAndPos(prettyDisplayAction(a2, problem), layerIdx, idxElmLayer);
                    addToAllVariables(varAction2);
                    universalConstrains.append("(assert (or (not " + varAction1 + ") (not " + varAction2 + ")))\n");
                }

                // Add the blank action as well if this elm can contain a blank action
                if (this.layers.get(layerIdx).layerElements.get(idxElmLayer).canContainsBlankAction()) {
                    String varBlankAction = addLayerAndPos(getBlankAction(), layerIdx, idxElmLayer);
                    addToAllVariables(varBlankAction);
                    universalConstrains.append("(assert (or (not " + varAction1 + ") (not " + varBlankAction + ")))\n");
                }
            }
        }

        return universalConstrains.toString();
    }


    private String addTransitionalClauses(int layerIdx) {

        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();
        StringBuilder transitionnalClauses = new StringBuilder();

        // Rule 10
        transitionnalClauses.append(rule10(layerIdx));

        // Rule 11
        transitionnalClauses.append(rule11(layerIdx));

        // Rule 12
        transitionnalClauses.append(rule12(layerIdx));

        // Rule 13 14 15
        transitionnalClauses.append(rule13_14_15(layerIdx));

        return transitionnalClauses.toString();

    }

    void addToAllVariables(String variable) {
        if (!this.allVariables.contains(variable)) {
            this.allVariables.add(variable);
        }
    }

    void writeIntoSMTFile(String clauses) throws IOException {
        BufferedWriter writer;

        writer = new BufferedWriter(new FileWriter(this.filenameSMTFile));

        writer.write("(set-logic QF_LIA)\n");
        writer.write("(set-option :produce-models true)\n");

        // Declare all the variables
        for (String var: this.allVariables) {
            writer.write("(declare-const " + var + " Bool)\n");
        }

        // Write the clauses
        writer.write(clauses);

        writer.write("(check-sat)\n");
        writer.write("(get-model)\n");
        writer.write("(exit)\n");
        writer.flush();
        writer.close();
    }

    public Vector<String> getAllVariables() {
        return this.allVariables;
    }

    public String getClauses() {
        return null;
    }


    // boolean checkIfFileIsSatisfiable(Problem problem) {

    //     long beginEncodeTime = System.currentTimeMillis();
    //     System.out.println("Launch solver on problem encoded");
    //     long endEncodeTime = System.currentTimeMillis();
    //     problem.getStatistics()
    //             .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

    //     long beginSolveTime = System.currentTimeMillis();
    //     String responseSolver = executeSMTSolverOnFile(filename);
    //     long endSolveTime = System.currentTimeMillis();
    //     this.getStatistics()
    //             .setTimeToSearch(this.getStatistics().getTimeToSearch() + (endSolveTime - beginSolveTime));
    //     if (fileIsSatisfiable(responseSolver)) {
    //         System.out.println("File is satisfiable !");
    //         // Extract plan from response
    //         SequentialPlan plan = extractPlanFromSolver(problem, responseSolver);
    //         return plan;
    //     }
    //     else {
    //         System.out.println("File is not satisfiable ");
    //         // Check sat here
    //         safe_check++;
    //         sizePlanToSearchFor++;
    //         beginEncodeTime = System.currentTimeMillis();
    //     }
    // }

    /**
     * Create the first layer and the layer element in it
    */
    public void initializeFirstLayerAndLayerElms() {
        Layer firstLayer = new Layer();

        

        for (int i = 0; i < this.problem.getInitialTaskNetwork().getTasks().size(); i++) {
            LayerElement layerElm = new LayerElement();
            firstLayer.layerElements.add(layerElm);
        }   
        
        // Add as well a layer element for the goal
        LayerElement finalLayerElm = new LayerElement();
        firstLayer.layerElements.add(finalLayerElm);

        this.layers.add(firstLayer);
    }

    /**
     * Create a new layer containing empty layer elements for each possible child of
     * the current layer
     * 
     * @param layerIdx
     */
    public void initializeNextLayerAndLayerElms() {

        Layer nextLayer = new Layer();

        int numberElmsInNextLayer = this.layers.lastElement().n.lastElement() + this.layers.lastElement().e.lastElement();

        for (int i = 0; i < numberElmsInNextLayer; i++) {
            LayerElement layerElm = new LayerElement();
            nextLayer.layerElements.add(layerElm);
        }
        this.layers.add(nextLayer);
    }

    public void computeNextandMaxAmountOfChildOfEachLayerElm(int idxLayer) {

        int firstChildPosition = 0;
        int maximumChildren = 0;
        Layer layer = this.layers.get(idxLayer);

        for (LayerElement layerElm: layer.layerElements) {

            layer.n.add(firstChildPosition);
            maximumChildren = layerElm.computeNumberChildren();
            layer.e.add(maximumChildren);

            firstChildPosition += maximumChildren;
        }
    }

    public void Encode() {

        StringBuilder fullClauses = new StringBuilder();
        initializeFirstLayerAndLayerElms();
        
        String initialStateConstrains = addInitialStateConstrains();

        int layerIdx = 0;
        String universalClauses = addUniversalConstrains(layerIdx);

        String allElementsArePrimitive = rule16(layerIdx);
        // Add initial clauses, universaleClauses and rule16 to full clauses
        fullClauses.append(initialStateConstrains);
        fullClauses.append(universalClauses);
        fullClauses.append(allElementsArePrimitive);

        // Try SMT Here
        try {
            writeIntoSMTFile(fullClauses.toString());
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // Remove the allElementsArePrimitive which correspond to 3 lines
        int numberOfLinesToDelete = 3;
        for (int i = 0; i < numberOfLinesToDelete; i++)
        {
            fullClauses.setLength(fullClauses.lastIndexOf("\n"));
        }
        fullClauses.append("\n");


        boolean fileIsSatisfiable = false;
        // Check if file is satisfiable here

        
        while (!fileIsSatisfiable) {

            layerIdx++;

            fullClauses.append("; ------- For layer " + layerIdx + " ------------\n");

            // Compute the n(l, i) and e(l, i) of the previous layer
            computeNextandMaxAmountOfChildOfEachLayerElm(layerIdx - 1);

            // Initialize new layer
            initializeNextLayerAndLayerElms();

            // Add transitionnal clauses from previous layer to current layer
            String transitionalClauses = addTransitionalClauses(layerIdx - 1);

            // Add the universal clauses for the current layer
            universalClauses = addUniversalConstrains(layerIdx);

            // Add the rule 16
            allElementsArePrimitive = rule16(layerIdx);


            fullClauses.append(transitionalClauses);
            fullClauses.append(universalClauses);

            fullClauses.append(allElementsArePrimitive);


            // Try SMT Here
            try {
                writeIntoSMTFile(fullClauses.toString());
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            // Remove the rule16
            for (int i = 0; i < numberOfLinesToDelete; i++)
            {
                fullClauses.setLength(fullClauses.lastIndexOf("\n"));
            }
            fullClauses.append("\n");
        }

        System.out.println("ICI");

    }

    public String encodeFirstLayer() {
        initializeFirstLayerAndLayerElms();
        
        System.out.println("Compute initial state clauses");
        String initialStateConstrains = addInitialStateConstrains();

        int layerIdx = 0;
        System.out.println("Compute universal clauses");
        String universalClauses = addUniversalConstrains(layerIdx);

        String allElementsArePrimitive = rule16(layerIdx);
        // Add initial clauses, universaleClauses and rule16 to full clauses

        this.allClauses.append(initialStateConstrains);
        this.allClauses.append(universalClauses);
        this.allClauses.append(allElementsArePrimitive);

        return this.allClauses.toString();
    }

    public String encodeNextLayer(int layerIdx) {

        // Remove the last three lines of all clauses since it is a formula retractable (rule16)
        int numberOfLinesToDelete = 3;
        for (int i = 0; i < numberOfLinesToDelete; i++)
        {
            this.allClauses.setLength(this.allClauses.lastIndexOf("\n"));
        }
        this.allClauses.append("\n");
        
        this.allClauses.append("; ------- For layer " + layerIdx + " ------------\n");

        // Compute the n(l, i) and e(l, i) of the previous layer
        computeNextandMaxAmountOfChildOfEachLayerElm(layerIdx - 1);

        // Initialize new layer
        initializeNextLayerAndLayerElms();

        // Add transitionnal clauses from previous layer to current layer
        System.out.println("Compute transitional clauses");
        String transitionalClauses = addTransitionalClauses(layerIdx - 1);

        // Add the universal clauses for the current layer
        System.out.println("Compute universal clauses");
        String universalClauses = addUniversalConstrains(layerIdx);

        // Add the rule 16
        String allElementsArePrimitive = rule16(layerIdx);


        this.allClauses.append(transitionalClauses);
        this.allClauses.append(universalClauses);
        this.allClauses.append(allElementsArePrimitive);

        return this.allClauses.toString();
    }
}

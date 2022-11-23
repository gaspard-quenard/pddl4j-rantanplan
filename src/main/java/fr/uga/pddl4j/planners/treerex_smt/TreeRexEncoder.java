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
import java.util.Collection;
import java.util.List;

import fr.uga.pddl4j.util.BitVector;

import fr.uga.pddl4j.parser.SAS_Plus.Strips2SasPlus;

enum VAR_TYPE {
    BOOLEAN,
    INTEGER
}

public class TreeRexEncoder {

    private final Problem problem;

    private int actionsSize;
    private int factsSize;
    private boolean useSASplus;
    private Vector<Layer> layers = new Vector<Layer>();

    // Used only if SAS+ is true in the function TreeRexEncoder
    List<List<Integer>> treerex_cliques;

    StringBuilder allClauses;
    Vector<String> allBoolVariables;
    Vector<String> allIntVariables;

    public TreeRexEncoder(Problem problem, boolean useSASplus) {
        this.problem = problem;

        this.actionsSize = this.problem.getActions().size();
        this.factsSize = this.problem.getFluents().size();
        this.allBoolVariables = new Vector<String>();
        this.allIntVariables = new Vector<String>();
        this.allClauses = new StringBuilder();
        this.useSASplus = useSASplus;

        if (useSASplus) {

            String domainName = problem.getParsedProblem().getProblemName().getValue(); // There is a bug, and the
                                                                                        // domain name is given by the
                                                                                        // method getProblemName()

            List<Collection<Integer>> cliques;
            // Since we know the cliques for gripper, let's calculate them here
            if (domainName.equals("gripper")) {
                cliques = new ArrayList<>();
                // For the gripper there are the following cliques:
                // Clique 0 -> all fluent which carry_ball<idxball>_left + carry_free_left
                // Clique 1 -> all fluent which carry_ball<idxball>_right + carry_free_right
                // Clique 2 -> robby-at rooma + robby-at roomb
                // Clique i for i in (3:num_ball+3) -> fluent_at_ball<i>_rooma +
                // fluent_at_ball<i>_roomb

                // First, determinate the number of balls
                int numberBalls = 0;
                for (String obj : problem.getConstantSymbols()) {
                    if (obj.startsWith("ball")) {
                        numberBalls++;
                    }
                }

                // Clique which indicate if the robot carry a ball with left hand
                List<Integer> cliqueCarryBallLeft = new ArrayList<>();
                cliques.add(cliqueCarryBallLeft);

                // Clique which indicate if the robot carry a ball with right hand
                List<Integer> cliqueBallRight = new ArrayList<>();
                cliques.add(cliqueBallRight);

                // Clique which indicate in which room the robot is
                List<Integer> cliqueRoomRobot = new ArrayList<>();
                cliques.add(cliqueRoomRobot);

                // Initialize the number of cliques
                for (int i = 0; i < numberBalls; i++) {
                    List<Integer> cliqueBall = new ArrayList<>();
                    cliques.add(cliqueBall);
                }

                // Iterate over all fluent and check in which clique this fluent correspond
                for (int i = 0; i < this.factsSize; i++) {
                    Fluent f = this.problem.getFluents().get(i);
                    String fluentString = prettyDisplayFluent(f, problem).substring(7);
                    // Add it to the correct clique
                    if (fluentString.endsWith("_left")) {
                        cliques.get(0).add(i);
                    } else if (fluentString.endsWith("_right")) {
                        cliques.get(1).add(i);
                    } else if (fluentString.startsWith("at-robby")) {
                        cliques.get(2).add(i);
                    } else if (fluentString.startsWith("at_ball")) {
                        String stringidxBall = fluentString.substring("at_ball".length());
                        stringidxBall = stringidxBall.substring(0, stringidxBall.indexOf('_'));
                        // The end of the string should be the next _
                        int idxBall = Integer.parseInt(stringidxBall); // The index of ball start at 1
                        cliques.get(2 + idxBall).add(i);
                    } else {
                        System.out.println("--- ERROR ----");
                    }
                }
            }

            else {
                Strips2SasPlus.callH2Hheuristic(problem);
                Strips2SasPlus.createFactSets(problem);
                Strips2SasPlus.greedyCovering(problem);
                cliques = Strips2SasPlus.cliques;
            }

            // Get only the cliques which have more than one elements
            this.treerex_cliques = new ArrayList<>();

            // Some debugging informations
            System.out.println("------------");
            Integer idxClique = 0;
            for (Collection<Integer> clique : cliques) {
                System.out.println("Clique " + idxClique + ": ");
                idxClique++;
                for (Integer i : clique) {
                    Fluent f = problem.getFluents().get(i);
                    System.out.println(prettyDisplayFluent(f, problem));
                }
                if (clique.size() > 1) {
                    this.treerex_cliques.add(new ArrayList<Integer>(clique));
                }
            }
            System.out.println("------------");
        }
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

    /**
     * Return a string containing a clique fluent in easily readable format
     * 
     * @param f       The clique fluent to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the fluent in easily readable format
     */
    private String prettyDisplayCliqueFluent(int idxClique, Problem problem) {
        StringBuilder cliqueFluentToDisplay = new StringBuilder();

        cliqueFluentToDisplay.append("CLIQUE_" + idxClique);

        return cliqueFluentToDisplay.toString();
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

    private boolean fluentIsClique(int idxFluent) {
        for (Collection<Integer> clique : this.treerex_cliques) {
            if (clique.contains(idxFluent)) {
                return true;
            }
        }
        return false;
    }

    public String addInitialStateConstrains() {

        StringBuilder constrainsInitState = new StringBuilder();

        String var;

        // RULE 1 -> Inital facts hold at position 0
        constrainsInitState.append("; rule 1: Initals facts hold at pos 0\n");

        // Compute first the initials facts for the SAS+ fluents
        if (this.useSASplus) {
            for (List<Integer> clique : this.treerex_cliques) {

                // Check for the fluent which is true among all fluents in the clique
                // there should be only one
                for (Integer idxFluent : clique) {
                    if (this.problem.getInitialState().getPositiveFluents().get(idxFluent)) {
                        Fluent f = this.problem.getFluents().get(idxFluent);
                        // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), 0, 0);
                        var = addLayerAndPos(prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem),
                                0, 0);
                        addToAllVariables(var);
                        this.layers.get(0).layerElements.get(0).addClique(clique);
                        constrainsInitState
                                .append("(assert (= " +
                                        var
                                        + " " + clique.indexOf(idxFluent) + "))\n");
                    }

                }
            }
        }

        for (int i = 0; i < this.factsSize; i++) {
            Fluent f = this.problem.getFluents().get(i);
            if (!this.useSASplus || !fluentIsClique(i)) {
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
        }

        constrainsInitState.append("; rule 2: Reduction initial task network\n");
        int number_elements_in_first_layer = this.problem.getInitialTaskNetwork().getTasks().size();
        // RULE 2 -> Get all reduction of the initial task networks.

        Layer layer0 = this.layers.get(0);

        for (int i = 0; i < this.problem.getInitialTaskNetwork().getTasks().size(); i++) {
            LayerElement layerElm = layer0.layerElements.get(i);

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
        // TODO do it for clique as well !
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

    /**
     * Rule 10: A fact p holds at some position i if and only if it also holds
     * at its first child position at the next hierarchical layer.
     * 
     * @param layerIdx Idx of the current layer
     * @return
     */
    private String rule10(int layerIdx) {

        int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();
        StringBuilder constrainsDescendants = new StringBuilder();
        constrainsDescendants.append("; rule 10: A fact also holds at its first child position\n");
        for (int layerElm = 0; layerElm < numberElementsInLayer; layerElm++) {
            int childLayerElm = this.layers.get(layerIdx).n.get(layerElm);

            if (this.useSASplus) {
                for (List<Integer> clique : this.layers.get(layerIdx).layerElements.get(layerElm).getFluentCliques()) {
                    // for (List<Integer> clique : this.treerex_cliques) {

                    Fluent f = this.problem.getFluents().get(this.treerex_cliques.indexOf(clique));

                    String varClique = addLayerAndPos(
                            prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem), layerIdx,
                            layerElm);

                    String varCliqueInChildLayer = addLayerAndPos(
                            prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem), layerIdx + 1,
                            childLayerElm);

                    addToAllVariables(varClique);
                    addToAllVariables(varCliqueInChildLayer);
                    this.layers.get(layerIdx + 1).layerElements.get(childLayerElm).addClique(clique);

                    constrainsDescendants.append("(assert (= " + varClique + " " + varCliqueInChildLayer + "))\n");
                }
            }
            // if (this.useSASplus) {
            // for (List<Integer> clique : this.treerex_cliques) {

            // String varClique =
            // addLayerAndPos(prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique),
            // problem), layerIdx, layerElm);

            // String varCliqueInChildLayer =
            // addLayerAndPos(prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique),
            // problem), layerIdx + 1,
            // childLayerElm);

            // addToAllVariables(varClique);
            // addToAllVariables(varCliqueInChildLayer);

            // constrainsDescendants.append("(assert (= " + varClique + " " +
            // varCliqueInChildLayer + "))\n");
            // }
            // }
            // Get all facts stored in the previous layer
            for (Fluent f : this.layers.get(layerIdx).layerElements.get(layerElm).getPositivesFluents()) {
                // for (int i = 0; i < this.factsSize; i++) {
                // if (!this.useSASplus || !fluentIsClique(i)) {
                // Fluent f = this.problem.getFluents().get(i);
                String varFluent = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx, layerElm);
                String varFluentInChildLayer = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx + 1,
                        childLayerElm);
                addToAllVariables(varFluent);
                addToAllVariables(varFluentInChildLayer);
                this.layers.get(layerIdx + 1).layerElements.get(childLayerElm).addPositiveFluent(f);
                constrainsDescendants.append("(assert (=> " + varFluent + " " + varFluentInChildLayer + "))\n");
                constrainsDescendants
                        .append("(assert (=> " + varFluentInChildLayer + " " + varFluent + "))\n");
                // }
            }
            for (Fluent f : this.layers.get(layerIdx).layerElements.get(layerElm).getNegativesFluents()) {
                // for (int i = 0; i < this.factsSize; i++) {
                // if (!this.useSASplus || !fluentIsClique(i)) {
                // Fluent f = this.problem.getFluents().get(i);
                String varFluent = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx, layerElm);
                String varFluentInChildLayer = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx + 1,
                        childLayerElm);
                addToAllVariables(varFluent);
                addToAllVariables(varFluentInChildLayer);
                this.layers.get(layerIdx + 1).layerElements.get(childLayerElm).addNegativeFluent(f);
                constrainsDescendants.append("(assert (=> " + varFluent + " " + varFluentInChildLayer + "))\n");
                constrainsDescendants
                        .append("(assert (=> " + varFluentInChildLayer + " " + varFluent + "))\n");
                // }
            }
        }

        return constrainsDescendants.toString();
    }

    // private String rule10(int layerIdx) {

    // int numberElementsInLayer = this.layers.get(layerIdx).layerElements.size();
    // StringBuilder constrainsDescendants = new StringBuilder();
    // constrainsDescendants.append("; rule 10: A fact also holds at its first child
    // position\n");
    // for (int layerElm = 0; layerElm < numberElementsInLayer; layerElm++) {
    // int childLayerElm = this.layers.get(layerIdx).n.get(layerElm);

    // if (this.useSASplus) {
    // for (List<Integer> clique : this.treerex_cliques) {

    // String varClique =
    // addLayerAndPos(prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique),
    // problem), layerIdx, layerElm);

    // String varCliqueInChildLayer =
    // addLayerAndPos(prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique),
    // problem), layerIdx + 1,
    // childLayerElm);

    // addToAllVariables(varClique);
    // addToAllVariables(varCliqueInChildLayer);

    // constrainsDescendants.append("(assert (= " + varClique + " " +
    // varCliqueInChildLayer + "))\n");
    // }
    // }
    // for (int i = 0; i < this.factsSize; i++) {
    // if (!this.useSASplus || !fluentIsClique(i)) {
    // Fluent f = this.problem.getFluents().get(i);
    // String varFluent = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx,
    // layerElm);
    // String varFluentInChildLayer = addLayerAndPos(prettyDisplayFluent(f,
    // problem), layerIdx + 1,
    // childLayerElm);
    // addToAllVariables(varFluent);
    // addToAllVariables(varFluentInChildLayer);
    // constrainsDescendants.append("(assert (=> " + varFluent + " " +
    // varFluentInChildLayer + "))\n");
    // constrainsDescendants
    // .append("(assert (=> " + varFluentInChildLayer + " " + varFluent + "))\n");
    // }
    // }
    // }

    // return constrainsDescendants.toString();
    // }

    /**
     * Rule 11: If an action occurs at some position i, then it will also occur
     * at its first child position at the next hierarchical layer.
     * 
     * @param layerIdx Idx of the current layer
     * @return
     */
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
                String varActionNextLayer = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx + 1,
                        childLayerElm);
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

    /**
     * Rule 12: If an action occurs at some position i, then all further child
     * positions at the next layer will contain a blank element.
     * 
     * @param layerIdx Index of the current layer
     * @return
     */
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
                        String varBlankAction = addLayerAndPos(getBlankAction(), layerIdx + 1,
                                firstPosChildElm + childIdx);
                        addToAllVariables(varBlankAction);
                        constrainsRule12
                                .append(varBlankAction + " ");

                        // TODO Should add blank action to layer here ?
                        // this.layers.get(layerIdx + 1).layerElements.get(firstPosChildElm +
                        // childIdx).addBlankAction();
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

    /**
     * Rule 13, 14, 15:
     * - Rule 13: If a reduction occurs at some position i, then it implies some
     * valid combination of its subtasks at the next layer. Reduction to action
     * - Rule 14: If a reduction occurs at some position i, then it implies some
     * valid combination of its subtasks at the next layer. Reduction to methods
     * - Rule 15: Any positions j at the next layer which remain undefined by an
     * occurring reduction are filled with blank symbols.
     * 
     * @param layerIdx Index of the current layer
     * @return
     */
    private String rule13_14_15(int layerIdx) {
        StringBuilder constrainsRule13_14_15 = new StringBuilder();
        constrainsRule13_14_15
                .append("; rule 13, 14, 15: Reduction to action, or to all subreduction of each subtasks\n");
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

                    // RULE 13 Reduction to actions
                    if (this.problem.getTasks().get(subtask).isPrimtive()) {
                        // Get the action which accomplish the method
                        Action a = this.problem.getActions().get(this.problem.getTaskResolvers().get(subtask).get(0));

                        String varActionNextLayer = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx + 1,
                                firstPosChildElm + i_subtask);

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
                                String varMethodNextLayer = addLayerAndPos(prettyDisplayMethod(subMethod, problem),
                                        layerIdx + 1, firstPosChildElm + i_subtask);
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

    /**
     * Rule 16: To find a plan after n layers, we must ensure that all the positions
     * of the last (i.e. the current) hierarchical layer n must be primitive.
     * 
     * @param layerIdx Index of the current layer
     * @return
     */
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

            Vector<Action> availableActionsForThisLayerAndPos = this.layers.get(layerIdx).layerElements.get(idxElmLayer)
                    .getActions();
            int nbAction = availableActionsForThisLayerAndPos.size();

            // Rule 5
            // Get all actions available for this layer elements
            universalConstrains.append("; rule 5: action implies precond and effects\n");
            for (Action action : this.layers.get(layerIdx).layerElements.get(idxElmLayer).getActions()) {

                if (action.getPrecondition().getPositiveFluents().length()
                        + action.getPrecondition().getNegativeFluents().length() == 0) {
                    continue;
                }
                String varAction = addLayerAndPos(prettyDisplayAction(action, problem), layerIdx, idxElmLayer);
                addToAllVariables(varAction);
                universalConstrains.append("(assert (=> "
                        + varAction + " (and ");

                // Do it for SAS+ var first
                if (this.useSASplus) {
                    for (List<Integer> clique : this.treerex_cliques) {

                        // Check for the fluent which is true among all fluents in the clique
                        // there should be only one
                        for (Integer idxFluent : clique) {
                            if (action.getPrecondition().getPositiveFluents().get(idxFluent)) {
                                Fluent f = this.problem.getFluents().get(idxFluent);
                                // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), layerIdx,
                                // idxElmLayer);
                                var = addLayerAndPos(
                                        prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem),
                                        layerIdx, idxElmLayer);
                                addToAllVariables(var);
                                this.layers.get(layerIdx).layerElements.get(idxElmLayer).addClique(clique);
                                universalConstrains
                                        .append("(= " +
                                                var
                                                + " " + clique.indexOf(idxFluent) + ") ");
                                continue;
                            }
                            if (action.getPrecondition().getNegativeFluents().get(idxFluent)) {
                                Fluent f = this.problem.getFluents().get(idxFluent);
                                // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), layerIdx,
                                // idxElmLayer);
                                var = addLayerAndPos(
                                        prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem),
                                        layerIdx, idxElmLayer);
                                addToAllVariables(var);
                                // this.layers.get(layerIdx).layerElements.get(idxElmLayer).addClique(clique);
                                // // TODO NOT SURE HERE...
                                universalConstrains
                                        .append("(not (= " +
                                                var
                                                + " " + clique.indexOf(idxFluent) + ")) ");
                                continue;
                            }

                        }
                    }
                }

                // Get the preconditions of the action
                for (int i = 0; i < this.factsSize; i++) {
                    if (!this.useSASplus || !fluentIsClique(i)) {
                        Fluent f = this.problem.getFluents().get(i);
                        if (action.getPrecondition().getPositiveFluents().get(i)) {
                            String fluentVar = prettyDisplayFluent(f, problem);
                            String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                            addToAllVariables(varFluent);
                            this.layers.get(layerIdx).layerElements.get(idxElmLayer).addPositiveFluent(f);
                            universalConstrains.append(varFluent + " ");
                        }
                        if (action.getPrecondition().getNegativeFluents().get(i)) {
                            String fluentVar = prettyDisplayFluent(f, problem);
                            String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                            addToAllVariables(varFluent);
                            this.layers.get(layerIdx).layerElements.get(idxElmLayer).addNegativeFluent(f);
                            universalConstrains
                                    .append("( not " + varFluent + " ) ");
                        }
                    }
                }
                universalConstrains.append(")))\n");

                // Add the effects of the actions as well
                universalConstrains.append("(assert (=> "
                        + varAction + " (and ");

                if (this.useSASplus) {
                    for (List<Integer> clique : this.treerex_cliques) {

                        // Check for the fluent which is true among all fluents in the clique
                        // there should be only one
                        for (Integer idxFluent : clique) {
                            if (action.getUnconditionalEffect().getPositiveFluents().get(idxFluent)) {
                                Fluent f = this.problem.getFluents().get(idxFluent);
                                // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), layerIdx,
                                // idxElmLayer + 1);
                                var = addLayerAndPos(
                                        prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem),
                                        layerIdx, idxElmLayer + 1);
                                addToAllVariables(var);
                                this.layers.get(layerIdx).layerElements.get(idxElmLayer + 1).addClique(clique);
                                universalConstrains
                                        .append("(= " +
                                                var
                                                + " " + clique.indexOf(idxFluent) + ") ");
                                continue;
                            }
                            if (action.getUnconditionalEffect().getNegativeFluents().get(idxFluent)) {
                                Fluent f = this.problem.getFluents().get(idxFluent);
                                // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), layerIdx,
                                // idxElmLayer + 1);
                                var = addLayerAndPos(
                                        prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem),
                                        layerIdx, idxElmLayer + 1);
                                addToAllVariables(var);
                                // this.layers.get(layerIdx).layerElements.get(idxElmLayer +
                                // 1).addClique(clique); // No need to add since its a negative effect, so it
                                // will remove the clique
                                universalConstrains
                                        .append("(not (= " +
                                                var
                                                + " " + clique.indexOf(idxFluent) + ")) ");
                                continue;
                            }

                        }
                    }
                }

                for (int i = 0; i < this.factsSize; i++) {
                    if (!this.useSASplus || !fluentIsClique(i)) {
                        Boolean factInPositiveFluent = false;
                        Fluent f = this.problem.getFluents().get(i);
                        if (action.getUnconditionalEffect().getPositiveFluents().get(i)) {
                            String fluentVar = prettyDisplayFluent(f, problem);
                            String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer + 1);
                            addToAllVariables(varFluent);
                            this.layers.get(layerIdx).layerElements.get(idxElmLayer + 1).addPositiveFluent(f);
                            universalConstrains.append(varFluent + " ");
                            factInPositiveFluent = true; // We have an incorect state if a fact is both a positive and
                                                         // negative fluent of an action (e.g: move f0 f0 -> lift at f0
                                                         // and
                                                         // not lift at f0 for the next element)
                        }
                        if (action.getUnconditionalEffect().getNegativeFluents().get(i) && !factInPositiveFluent) {
                            String fluentVar = prettyDisplayFluent(f, problem);
                            String varFluent = addLayerAndPos(fluentVar, layerIdx, idxElmLayer + 1);
                            addToAllVariables(varFluent);
                            this.layers.get(layerIdx).layerElements.get(idxElmLayer + 1).addNegativeFluent(f);
                            universalConstrains
                                    .append("( not " + varFluent + " ) ");
                        }
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
                        + var + " (and true "); // True is used to have a correct file event if there is no
                                                // preconditions

                if (this.useSASplus) {
                    for (List<Integer> clique : this.treerex_cliques) {

                        // Check for the fluent which is true among all fluents in the clique
                        // there should be only one
                        for (Integer idxFluent : clique) {
                            if (method.getPrecondition().getPositiveFluents().get(idxFluent)) {
                                Fluent f = this.problem.getFluents().get(idxFluent);
                                // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), layerIdx,
                                // idxElmLayer);
                                var = addLayerAndPos(
                                        prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem),
                                        layerIdx, idxElmLayer);
                                addToAllVariables(var);
                                this.layers.get(layerIdx).layerElements.get(idxElmLayer).addClique(clique);
                                universalConstrains
                                        .append("(= " +
                                                var
                                                + " " + clique.indexOf(idxFluent) + ") ");
                                continue;
                            }
                            if (method.getPrecondition().getNegativeFluents().get(idxFluent)) {
                                Fluent f = this.problem.getFluents().get(idxFluent);
                                // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), layerIdx,
                                // idxElmLayer);
                                var = addLayerAndPos(
                                        prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem),
                                        layerIdx, idxElmLayer);
                                addToAllVariables(var);
                                this.layers.get(layerIdx).layerElements.get(idxElmLayer).addClique(clique);
                                universalConstrains
                                        .append("(not (= " +
                                                var
                                                + " " + clique.indexOf(idxFluent) + ")) ");
                                continue;
                            }

                        }
                    }
                }

                // Get the positives preconditions of the action
                for (int i = 0; i < this.factsSize; i++) {
                    if (!this.useSASplus || !fluentIsClique(i)) {
                        Fluent f = this.problem.getFluents().get(i);
                        if (method.getPrecondition().getPositiveFluents().get(i)) {
                            String fluentVar = prettyDisplayFluent(f, problem);
                            var = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                            addToAllVariables(var);
                            this.layers.get(layerIdx).layerElements.get(idxElmLayer).addPositiveFluent(f);
                            universalConstrains.append(var + " ");
                        }
                        if (method.getPrecondition().getNegativeFluents().get(i)) {
                            String fluentVar = prettyDisplayFluent(f, problem);
                            var = addLayerAndPos(fluentVar, layerIdx, idxElmLayer);
                            addToAllVariables(var);
                            this.layers.get(layerIdx).layerElements.get(idxElmLayer).addNegativeFluent(f);
                            universalConstrains.append("(not " + var + ") ");
                        }
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

            // Rule 9
            universalConstrains.append("; rule 9: At most one action\n");
            for (int i = 0; i < nbAction; i++) {
                Action a1 = availableActionsForThisLayerAndPos.get(i);
                String varAction1 = addLayerAndPos(prettyDisplayAction(a1, problem), layerIdx, idxElmLayer);
                addToAllVariables(varAction1);
                for (int j = i + 1; j < nbAction; j++) {
                    Action a2 = availableActionsForThisLayerAndPos.get(j);
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

        // Add frame axioms (should be done after the other actions with the
        // optimization since we need to know each fact possible at each position (which
        // are
        // computed dynamically with the rules 5 and 6 (precondiation and effects of
        // possibles actions)))
        for (int idxElmLayer = 0; idxElmLayer < numberElementsInLayer; idxElmLayer++) {
            // Rule 8
            universalConstrains.append(
                    "; For element " + idxElmLayer + "/" + (numberElementsInLayer - 1) + " rule 8: frame axioms\n");

            Vector<Action> availableActionsForThisLayerAndPos = this.layers.get(layerIdx).layerElements.get(idxElmLayer)
                    .getActions();
            int nbAction = availableActionsForThisLayerAndPos.size();

            if (idxElmLayer < numberElementsInLayer - 1) {

                if (this.useSASplus) {
                    // for (List<Integer> clique : this.treerex_cliques) {

                    // BIG OPTIMIZATION HERE. Instead of using the frame axioms for neighbooring
                    // position, 'jump' to a position where the predicate can change (in the same
                    // layer)
                    for (List<Integer> clique : this.layers.get(layerIdx).layerElements.get(idxElmLayer)
                            .getFluentCliques()) {

                        int IdxNext = idxElmLayer + 1;
                        // Find the next change in this clique
                        for (int nxtLayer = idxElmLayer + 1; nxtLayer < this.layers.get(layerIdx).layerElements
                                .size(); nxtLayer++) {
                            if (this.layers.get(layerIdx).layerElements.get(nxtLayer).getFluentCliques()
                                    .contains(clique)) {
                                IdxNext = nxtLayer;
                                break;
                            }
                        }

                        // int IdxNext = idxElmLayer + 1;

                        String varClique = addLayerAndPos(
                                prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem), layerIdx,
                                idxElmLayer);
                        String varNextClique = addLayerAndPos(
                                prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique), problem), layerIdx,
                                IdxNext);
                        this.addToAllVariables(varClique);
                        this.addToAllVariables(varNextClique);
                        String varPrimitivePred = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
                        universalConstrains.append("(assert (=> (not (= " + varClique + " " + varNextClique + ")) ");
                        universalConstrains.append("(or (not " + varPrimitivePred + ") ");
                        // Check for the fluent which is true among all fluents in the clique
                        // there should be only one
                        for (Integer idxFluent : clique) {

                            for (Action a : availableActionsForThisLayerAndPos) {
                                if (a.getUnconditionalEffect().getNegativeFluents().get(idxFluent)
                                        || a.getUnconditionalEffect().getPositiveFluents().get(idxFluent)) {
                                    String varAction = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx,
                                            idxElmLayer);
                                    addToAllVariables(varAction);
                                    universalConstrains.append(varAction + " ");
                                }
                            }
                        }
                        universalConstrains.append(")))\n");
                    }
                }

                for (int i = 0; i < this.factsSize; i++) {
                    // if (!this.useSASplus || !fluentIsClique(i)) {
                    Fluent f = this.problem.getFluents().get(i);
                    if (this.layers.get(layerIdx).layerElements.get(idxElmLayer).getPositivesFluents().contains(f)) {
                        String varFluent = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx, idxElmLayer);


                        // Find the next change of this fact
                        int IdxNext = idxElmLayer + 1;

                        for (int nxtLayer = idxElmLayer + 1; nxtLayer < this.layers.get(layerIdx).layerElements.size(); nxtLayer++) {
                            if (this.layers.get(layerIdx).layerElements.get(nxtLayer).getPositivesFluents()
                                    .contains(f)) {
                                IdxNext = nxtLayer;
                                break;
                            }
                        }

                        String varFluentNextElm = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx,
                        IdxNext);
                        String varPrimitivePred = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
                        addToAllVariables(varFluent);
                        addToAllVariables(varFluentNextElm);

                        universalConstrains
                                .append("(assert (=> (and " + varFluent + " (not " + varFluentNextElm + ")) ");

                        universalConstrains.append("(or (not " + varPrimitivePred + ") ");
                        for (Action a : availableActionsForThisLayerAndPos) {
                            if (a.getUnconditionalEffect().getNegativeFluents().get(i)) {
                                String varAction = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx,
                                        idxElmLayer);
                                addToAllVariables(varAction);
                                universalConstrains.append(varAction + " ");
                            }
                        }
                        universalConstrains.append(")))\n");
                    }
                    if (this.layers.get(layerIdx).layerElements.get(idxElmLayer).getNegativesFluents().contains(f)) {
                        String varFluent = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx, idxElmLayer);

                        // Find the next change of this fact
                        int IdxNext = idxElmLayer + 1;

                        for (int nxtLayer = idxElmLayer + 1; nxtLayer < this.layers.get(layerIdx).layerElements.size(); nxtLayer++) {
                            if (this.layers.get(layerIdx).layerElements.get(nxtLayer).getNegativesFluents()
                                    .contains(f)) {
                                IdxNext = nxtLayer;
                                break;
                            }
                        }

                        String varFluentNextElm = addLayerAndPos(prettyDisplayFluent(f, problem), layerIdx,
                                IdxNext);
                        String varPrimitivePred = addLayerAndPos(getPrimitivePredicate(), layerIdx, idxElmLayer);
                        addToAllVariables(varFluent);
                        addToAllVariables(varFluentNextElm);

                        universalConstrains
                                .append("(assert (=> (and (not " + varFluent + ") " + varFluentNextElm + ") ");

                        universalConstrains.append("(or (not " + varPrimitivePred + ") ");
                        for (Action a : availableActionsForThisLayerAndPos) {
                            if (a.getUnconditionalEffect().getPositiveFluents().get(i)) {
                                String varAction = addLayerAndPos(prettyDisplayAction(a, problem), layerIdx,
                                        idxElmLayer);
                                addToAllVariables(varAction);
                                universalConstrains.append(varAction + " ");
                            }
                        }
                        universalConstrains.append(")))\n");
                    }
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

        VAR_TYPE var_type = VAR_TYPE.BOOLEAN;
        if (variable.startsWith("CLIQUE")) {
            var_type = VAR_TYPE.INTEGER;
        }

        if (var_type == VAR_TYPE.BOOLEAN) {
            if (!this.allBoolVariables.contains(variable)) {
                this.allBoolVariables.add(variable);
            }
        } else if (var_type == VAR_TYPE.INTEGER) {
            if (!this.allIntVariables.contains(variable)) {
                this.allIntVariables.add(variable);
            }
        }
    }

    public Vector<String> getAllBoolVariables() {
        return this.allBoolVariables;
    }

    public Vector<String> getAllIntVariables() {
        return this.allIntVariables;
    }

    public String getClauses() {
        return null;
    }

    public int getLastLayerSize() {
        return this.layers.lastElement().layerElements.size();
    }

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

        int numberElmsInNextLayer = this.layers.lastElement().n.lastElement()
                + this.layers.lastElement().e.lastElement();

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

        for (LayerElement layerElm : layer.layerElements) {

            layer.n.add(firstChildPosition);
            maximumChildren = layerElm.computeNumberChildren();
            layer.e.add(maximumChildren);

            firstChildPosition += maximumChildren;
        }
    }

    public String encodeFirstLayer() {
        initializeFirstLayerAndLayerElms();

        System.out.println("Compute initial state clauses");
        String initialStateConstrains = addInitialStateConstrains();

        int layerIdx = 0;
        System.out.println("Compute universal clauses");
        String universalClauses = addUniversalConstrains(layerIdx);

        System.out.println("Add rule 16 (verify that there is an action at each position of the current layer)");
        String allElementsArePrimitive = rule16(layerIdx);
        // Add initial clauses, universaleClauses and rule16 to full clauses

        System.out.println("Add all clauses to list clauses");
        this.allClauses.append(initialStateConstrains);
        this.allClauses.append(universalClauses);
        this.allClauses.append(allElementsArePrimitive);

        return this.allClauses.toString();
    }

    public String encodeNextLayer(int layerIdx) {

        // Remove the last three lines of all clauses since it is a formula retractable
        // (rule16)
        int numberOfLinesToDelete = 3;
        for (int i = 0; i < numberOfLinesToDelete; i++) {
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
        System.out.println("Add rule 16 (verify that there is an action at each position of the current layer)");
        String allElementsArePrimitive = rule16(layerIdx);

        System.out.println("Add all clauses to list clauses");
        this.allClauses.append(transitionalClauses);
        this.allClauses.append(universalClauses);
        this.allClauses.append(allElementsArePrimitive);

        return this.allClauses.toString();
    }
}

package fr.uga.pddl4j.planners.lilotane;

import java.util.Vector;

import javax.lang.model.element.Element;

import org.apache.commons.lang3.ThreadUtils.NamePredicate;
import org.sat4j.ExitCode;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.uga.pddl4j.util.BitVector;
import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.NamedTypedList;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.ParsedMethod;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.TypedSymbol;
import fr.uga.pddl4j.parser.SAS_Plus.SASplusLiftedFamGroup;
// import fr.uga.pddl4j.parser.SAS_Plus.SASPlusGeneratorDomain;
import fr.uga.pddl4j.parser.SAS_Plus.Strips2SasPlus;

enum VAR_TYPE {
    BOOLEAN,
    INTEGER
}

public class LilotaneEncoder {

    private final Problem problem;

    private int actionsSize;
    private int factsSize;
    public Vector<Layer> layers = new Vector<Layer>();
    // Array which map a method idx (the idx of the array) to the set of facts idxs
    // that this method can
    // change
    private Set<Integer>[] methodIdxToFactsIdxChangedByMethod;
    // Dictionary which map a fluent idx to the index of the clique which contains
    // it
    Map<Integer, Integer> dictFluentIdxToCliqueIdx;

    Map<String, HashSet<Fluent>> dictStaticPredicateNameToAllFluentWithThisPredicate;

    // Used only if SAS+ is true in the function TreeRexEncoder
    List<List<Integer>> treerex_cliques;

    Set<String> staticPredicates;

    HashSet<ScopeVariable> allScopeVariables;
    HashSet<ScopeVariable> scopeVariablesAlreadyDeclared;

    Map<String, Vector<String>> dictTypeToObjects;
    Map<String, String> dictObjNameToType;
    Map<String, Integer> liftedMethodToNumberSubtasks;

    Map<String, ParsedMethod> methodNameToObj;
    Map<String, ParsedAction> actionNameToObj;

    Map<String, HashSet<String>> dictGroundPredToLiftedActionWithGroundPredAsPosEff;
    Map<String, HashSet<String>> dictGroundPredToLiftedActionWithGroundPredAsNegEff;

    Map<String, Map<String, ArrayList<Integer>>> dictIdxArgPredToIdxArgActionAssociatedPosEff;
    Map<String, Map<String, ArrayList<Integer>>> dictIdxArgPredToIdxArgActionAssociatedNegEff;

    private Map<String, HashSet<String>> dictTypeToChildTypes;
    private Map<String, HashSet<String>> dictTypeToParentTypes;

    private LilotaneOptimization optimizationsToUse;

    HashSet<LiftedAction> allLiftedActionsLastLayer;

    StringBuilder allClauses;
    public StringBuilder declarationObjectsAndPredicates;
    Vector<String> allBoolVariables;
    Vector<String> allIntVariables;
    public Map<String, ArrayList<HashSet<String>>> allActionsWithScopeVariables;

    public LilotaneEncoder(Problem problem, LilotaneOptimization optimizationsTouse) {
        this.problem = problem;

        this.actionsSize = this.problem.getActions().size();
        this.factsSize = this.problem.getFluents().size();
        this.allBoolVariables = new Vector<String>();
        this.allIntVariables = new Vector<String>();
        this.allActionsWithScopeVariables = new HashMap<String, ArrayList<HashSet<String>>>();

        this.dictStaticPredicateNameToAllFluentWithThisPredicate = new HashMap<String, HashSet<Fluent>>();

        this.allClauses = new StringBuilder();
        this.declarationObjectsAndPredicates = new StringBuilder();
        this.dictFluentIdxToCliqueIdx = new HashMap<>();
        this.optimizationsToUse = optimizationsTouse;
        this.allLiftedActionsLastLayer = new HashSet<LiftedAction>();

        this.allScopeVariables = new HashSet<ScopeVariable>();
        this.scopeVariablesAlreadyDeclared = new HashSet<ScopeVariable>();

        System.out.println("Do some preprocessing...");
        long beginPreprocessingTime = System.currentTimeMillis();
        methodIdxToFactsIdxChangedByMethod = generateDictMethodsToFactsChangedByMethod();

        preprocessingComputeAllParentsAndChildrenEachTypes();

        this.dictObjNameToType = new HashMap<String, String>();
        // Find each object and give a value for each object of each type
        this.dictTypeToObjects = new HashMap<String, Vector<String>>();
        for (String typeName : this.problem.getTypes()) {
            this.dictTypeToObjects.put(typeName, new Vector<String>());
        }
        // Now iterate over each object to get the type
        for (TypedSymbol<String> obj : this.problem.getParsedProblem().getConstants()) {
            String nameObj = obj.getValue();
            String typeObj = obj.getTypes().get(0).getValue();
            System.out.println(nameObj + " " + typeObj);
            this.dictTypeToObjects.get(typeObj).add(nameObj);
            this.dictObjNameToType.put(nameObj, typeObj);
        }

        // For each method, map its name to the object parsed method associated
        // + For each method, compute the number of children that this method can take
        this.methodNameToObj = new HashMap<String, ParsedMethod>();
        this.liftedMethodToNumberSubtasks = new HashMap<String, Integer>();
        for (ParsedMethod methodObj : this.problem.getParsedProblem().getMethods()) {
            String nameMethod = methodObj.getName().getValue();
            this.methodNameToObj.put(nameMethod, methodObj);

            // Ugly way to get the number of subtasks of a lifted method, but it is done
            // only once, so who care
            for (Method m : problem.getMethods()) {
                if (m.getName().equals(nameMethod)) {
                    this.liftedMethodToNumberSubtasks.put(nameMethod, m.getSubTasks().size());
                    break;
                }
            }
        }

        this.dictIdxArgPredToIdxArgActionAssociatedPosEff = new HashMap<String, Map<String, ArrayList<Integer>>>();
        this.dictIdxArgPredToIdxArgActionAssociatedNegEff = new HashMap<String, Map<String, ArrayList<Integer>>>();
        for (String predName : problem.getPredicateSymbols()) {
            this.dictIdxArgPredToIdxArgActionAssociatedPosEff.put(predName, new HashMap<String, ArrayList<Integer>>());
            this.dictIdxArgPredToIdxArgActionAssociatedNegEff.put(predName, new HashMap<String, ArrayList<Integer>>());
        }

        this.actionNameToObj = new HashMap<String, ParsedAction>();
        for (ParsedAction actionObj : this.problem.getParsedProblem().getActions()) {
            String nameAction = actionObj.getName().getValue();
            this.actionNameToObj.put(nameAction, actionObj);

            // Iterate over all positive and negative predicate of this parsed action
            int numberEffActions = actionObj.getEffects().getChildren().size();
            if (numberEffActions == 0 && actionObj.getEffects().getSymbol() != null) {
                numberEffActions = 1;
            }

            // Iterate over all positive effects of the parsedAction
            for (int posEffId = 0; posEffId < numberEffActions; posEffId++) {

                Expression<String> effAction;
                if (numberEffActions > 1) {
                    effAction = actionObj.getEffects().getChildren().get(posEffId);
                } else {
                    effAction = actionObj.getEffects();
                }

                String predicateName;

                boolean isPositiveEff = true;

                if (effAction.getConnector().getImage().equals("not")) {

                    effAction = effAction.getChildren().get(0);
                    predicateName = effAction.getSymbol().getValue();
                    if (this.dictIdxArgPredToIdxArgActionAssociatedNegEff.get(predicateName).get(nameAction) == null) {
                        this.dictIdxArgPredToIdxArgActionAssociatedNegEff.get(predicateName).put(nameAction,
                                new ArrayList<Integer>());
                    }
                    isPositiveEff = false;
                } else {
                    predicateName = effAction.getSymbol().getValue();
                    if (this.dictIdxArgPredToIdxArgActionAssociatedPosEff.get(predicateName).get(nameAction) == null) {
                        this.dictIdxArgPredToIdxArgActionAssociatedPosEff.get(predicateName).put(nameAction,
                                new ArrayList<Integer>());
                    }
                }

                // Iterate over the argument of this predicate
                for (int idxArgEff = 0; idxArgEff < effAction.getArguments().size(); idxArgEff++) {
                    // Get the name of the parameter
                    String parameter = effAction.getArguments().get(idxArgEff).getValue();

                    // Parameters is in the form ?X<idx_of_paramter_of_action>. We want to get the
                    // idx of parameter of the action
                    int idxParamterAction = Integer.parseInt(parameter.substring(2));

                    if (isPositiveEff)
                        this.dictIdxArgPredToIdxArgActionAssociatedPosEff.get(predicateName).get(nameAction)
                                .add(idxParamterAction);
                    else
                        this.dictIdxArgPredToIdxArgActionAssociatedNegEff.get(predicateName).get(nameAction)
                                .add(idxParamterAction);
                }
            }
        }

        preprocessingComputeLiftedActionsSupportOfGroundPredicates(problem);

        // Get all the static predicates
        this.staticPredicates = preprocessingComputeStaticPredicates(problem);

        long deltaEncodingTime = System.currentTimeMillis() - beginPreprocessingTime;
        System.out.println("Delta preprocessing time " + deltaEncodingTime + " ms");

        if (this.optimizationsToUse.useSASplus) {

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
                // Strips2SasPlus.callH2Hheuristic(problem);
                // Strips2SasPlus.createFactSets(problem);
                // Strips2SasPlus.greedyCovering(problem);
                // cliques = Strips2SasPlus.cliques;

                SASplusLiftedFamGroup.determinateLiftedFamGroups(problem);
                cliques = SASplusLiftedFamGroup.cliques;
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
            // SASPlusGeneratorDomain.generatlizeInstantiationSASPlusForDomain(problem,
            // cliques);

            // Compute a dictionary which map the fluent Idx to the cliqueIdx to speed up
            // some following calculus
            for (int idx = 0; idx < this.treerex_cliques.size(); idx++) {
                for (Integer fluentIdx : this.treerex_cliques.get(idx)) {
                    this.dictFluentIdxToCliqueIdx.put(fluentIdx, idx);
                }
            }
        }
    }

    private static boolean predicatIsStatic(String predicateToCheck, Problem problem) {

        // Iterate over all action of our problem (in a lifted way)
        for (ParsedAction action : problem.getParsedProblem().getActions()) {

            // If the action only have one effect, check if this effect affect the predicate
            if (action.getEffects().getSymbol() != null && action.getEffects().getSymbol().equals(predicateToCheck)) {
                return false;
            }

            // Else Iterate over all effects of this action
            for (int effId = 0; effId < action.getEffects().getChildren().size(); effId++) {

                String predicateModifiedByAction = null;

                // Get the name of the predicate that will be modified by this effect
                if (action.getEffects().getChildren().get(effId).getConnector().getImage()
                        .equals("not")) {

                    predicateModifiedByAction = action.getEffects().getChildren().get(effId).getChildren().get(0)
                            .getSymbol().getValue();
                } else {
                    predicateModifiedByAction = action.getEffects().getChildren().get(effId).getSymbol().getValue();
                }

                if (predicateModifiedByAction.equals(predicateToCheck)) {
                    return false;
                }
            }
        }
        return true;
    }

    private static HashSet<String> preprocessingComputeStaticPredicates(Problem problem) {

        HashSet<String> staticPredicates = new HashSet<String>();
        // Iterate over all predicates name
        for (String predicateName : problem.getPredicateSymbols()) {
            if (predicatIsStatic(predicateName, problem)) {
                staticPredicates.add(predicateName);
            }
        }
        return staticPredicates;
    }

    /**
     * Generates a dictionary mapping methods to the set of facts that can be
     * changed by the method.
     * The methods included in the dictionary are determined by the initial tasks.
     *
     * @return a dictionary mapping methods to the set of facts that can be changed
     *         by the method
     */
    public Set<Integer>[] generateDictMethodsToFactsChangedByMethod() {
        // Create a list where each element of id i contains the set of the index of
        // facts which can be changed by
        // the method with index i
        int numberMethods = this.problem.getMethods().size();
        Set<Integer>[] dict = (Set<Integer>[]) new Set[numberMethods];

        //
        HashSet<Integer> checkedMethods = new HashSet<>();

        // Iterate over the initial tasks
        this.problem.getInitialTaskNetwork().getTasks().forEach(taskIndex -> {
            // Find all methods that can solve the current task
            this.problem.getMethods().stream()
                    .filter(method -> method.getTask() == taskIndex)
                    // Get the set of facts the method can change and add it to the dictionary
                    .forEach(method -> recursiveGetFactsChangedByMethod(this.problem.getMethods().indexOf(method), dict,
                            checkedMethods));
        });

        // printDictMethodsToFactsChangedByMethod(dict);

        // Return the dictionary
        return dict;
    }

    /**
     * Prints the results of the dictionary generated by the
     * generateDictMethodsToFactsChangedByMethod function.
     *
     * @param dict a dictionary mapping methods to the set of facts that can be
     *             changed by the method
     */
    public void printDictMethodsToFactsChangedByMethod(Set<Integer>[] dict) {
        for (int idxMethod = 0; idxMethod < this.problem.getMethods().size(); idxMethod++) {
            if (dict[idxMethod] != null) {
                Method method = this.problem.getMethods().get(idxMethod);
                System.out.println(
                        "Facts that can be changed by the method: " + this.prettyDisplayMethod(method, problem));
                for (Integer idxFluent : dict[idxMethod]) {
                    System.out.println("    " + prettyDisplayFluent(this.problem.getFluents().get(idxFluent), problem));
                }
            }
        }
    }

    /**
     * Recursively calculates the set of fluents that may be modified by the given
     * method
     * 
     * @param method the method to analyze
     * @param d      a dictionary mapping methods to the set of fluents that may be
     *               modified by the method
     * @return a set of fluents that may be modified by the given method
     */
    Set<Integer> recursiveGetFactsChangedByMethod(Integer idxMethod, Set<Integer>[] d,
            Set<Integer> checkedMethods) {

        // If the method has already been analyzed, return the set of fluents it can
        // modify
        if (d[idxMethod] != null) {
            return d[idxMethod];
        }

        // Add the method to the set of checked methods
        checkedMethods.add(idxMethod);

        // Set to store the fluents that may be modified by the method
        Set<Integer> factsChangedByMethod = new HashSet<Integer>();

        // Iterate over all subtasks of the method
        for (Integer subtaskIdx : this.problem.getMethods().get(idxMethod).getSubTasks()) {

            // Get the subtask object
            Task subtask = this.problem.getTasks().get(subtaskIdx);

            if (subtask.isPrimtive()) {
                // If subtask is primitive (decomposable into action), update the variable
                // facts_changed_by_method with all the predicates that can be changed by the
                // action

                // Get the action which accomplish the method
                Action action = this.problem.getActions().get(this.problem.getTaskResolvers().get(subtaskIdx).get(0));

                // Iterate over all the positive and negative effects of the action to
                // determinate the facts that can be changed by this action
                BitVector actionEffectPositiveFluents = action.getUnconditionalEffect().getPositiveFluents();

                for (int p = actionEffectPositiveFluents.nextSetBit(0); p >= 0; p = actionEffectPositiveFluents
                        .nextSetBit(p + 1)) {
                    factsChangedByMethod.add(p);
                    actionEffectPositiveFluents.set(p);
                }

                BitVector actionNegativesFluents = action.getUnconditionalEffect().getNegativeFluents();
                for (int p = actionNegativesFluents.nextSetBit(0); p >= 0; p = actionNegativesFluents
                        .nextSetBit(p + 1)) {
                    factsChangedByMethod.add(p);
                    actionNegativesFluents.set(p);
                }

            } else {
                // If the subtask is not primitive, find all methods which can resolve this
                // subtask and call the recursive_get_facts_changed_by_method function on each
                // of them

                // Get all the methods which can solve this task
                for (Method subMethod : problem.getMethods()) {
                    if (subMethod.getTask() == subtaskIdx) {

                        Integer idxSubMethod = this.problem.getMethods().indexOf(subMethod);

                        // If the method has not already been checked (to prevent infinite recursion)
                        if (!checkedMethods.contains(idxSubMethod)) {
                            // Call the recursive_get_facts_changed_by_method to get the facts changed by
                            // this method
                            factsChangedByMethod
                                    .addAll(recursiveGetFactsChangedByMethod(idxSubMethod, d, checkedMethods));
                        }
                    }
                }
            }
        }

        // Add the mapping from the method to the set of fluents it can modify to the
        // dictionary
        // d.put(method, factsChangedByMethod);
        d[idxMethod] = factsChangedByMethod;

        return factsChangedByMethod;
    }

    /**
     * For each ground predicate, find the set of lifted action which can have this
     * predicate
     * as positive effect of negative effect
     * 
     * @param problem
     */
    private void preprocessingComputeLiftedActionsSupportOfGroundPredicates(Problem problem) {

        // Initialize the dicts
        this.dictGroundPredToLiftedActionWithGroundPredAsPosEff = new HashMap<String, HashSet<String>>();
        this.dictGroundPredToLiftedActionWithGroundPredAsNegEff = new HashMap<String, HashSet<String>>();
        for (Fluent groundPred : this.problem.getFluents()) {
            String nameGroundPred = prettyDisplayFluent(groundPred, problem);
            this.dictGroundPredToLiftedActionWithGroundPredAsPosEff.put(nameGroundPred, new HashSet<String>());
            this.dictGroundPredToLiftedActionWithGroundPredAsNegEff.put(nameGroundPred, new HashSet<String>());
        }

        // Iterate over each lifted action
        for (ParsedAction liftedAction : problem.getParsedProblem().getActions()) {

            String liftedActionName = liftedAction.getName().getValue();

            // Iterate over all positive and negative predicate of this parsed action
            int numberEffActions = liftedAction.getEffects().getChildren().size();
            if (numberEffActions == 0 && liftedAction.getEffects().getSymbol() != null) {
                numberEffActions = 1;
            }

            // Iterate over all positive effects of the parsedAction
            for (int posEffId = 0; posEffId < numberEffActions; posEffId++) {

                Expression<String> effAction;
                if (numberEffActions > 1) {
                    effAction = liftedAction.getEffects().getChildren().get(posEffId);
                } else {
                    effAction = liftedAction.getEffects();
                }

                boolean isPositiveEff = true;

                if (effAction.getConnector().getImage().equals("not")) {

                    effAction = effAction.getChildren().get(0);
                    isPositiveEff = false;
                }

                String predicateName = effAction.getSymbol().getValue();

                // We need to get the type of each argument of this predicate
                ArrayList<String> typeNameOfEachArgs = new ArrayList<String>();

                // Iterate over the argument of this predicate
                for (int idxArgEff = 0; idxArgEff < effAction.getArguments().size(); idxArgEff++) {
                    // Get the name of the parameter
                    String parameter = effAction.getArguments().get(idxArgEff).getValue();

                    // Parameters is in the form ?X<idx_of_paramter_of_action>. We want to get the
                    // idx of parameter of the action
                    int idxParamterAction = Integer.parseInt(parameter.substring(2));
                    String nameTypeArg = liftedAction.getParameters().get(idxParamterAction).getTypes().get(0)
                            .getValue();
                    typeNameOfEachArgs.add(nameTypeArg);
                }

                // Find all the values that can take each argument of this predicate
                ArrayList<HashSet<String>> allValuesOfEachArgs = new ArrayList<HashSet<String>>();
                for (int i = 0; i < typeNameOfEachArgs.size(); i++) {
                    String typeNameofArg = typeNameOfEachArgs.get(i);
                    // We have to add all the values of this type and all the values of the
                    // subtypes of this type
                    HashSet<String> allValuesOfThisArg = new HashSet<String>();
                    allValuesOfThisArg.addAll(this.dictTypeToObjects.get(typeNameofArg));
                    for (String subType : this.dictTypeToChildTypes.get(typeNameofArg)) {
                        allValuesOfThisArg.addAll(this.dictTypeToObjects.get(subType));
                    }
                    allValuesOfEachArgs.add(allValuesOfThisArg);
                }

                // Now, we have to ground this predicate with all the possible values of the
                // arguments and add this lifted action to the set of lifted action which can
                // have this predicate as positive/negative effect
                recursiveGroundPredicateToAllPositibleValues(liftedActionName, predicateName, allValuesOfEachArgs,
                        new ArrayList<String>(), 0, isPositiveEff);
            }

        }
    }

    /**
     * Recursive function to find all the possible ground predicates of a predicate,
     * and indicate
     * the lifted function which can have these ground predicates as
     * positive/negative effect.
     * 
     */
    public void recursiveGroundPredicateToAllPositibleValues(String nameLiftedAction, String namePredicate,
            ArrayList<HashSet<String>> allPossibleValuesForEachArgOfThisPredicate,
            ArrayList<String> valueTakenByEachArgsOfPredicate, int idxArg, boolean predicateIsPositive) {

        // If we have already taken a value for each argument of this predicate, we can
        // add
        // this predicate to the set of predicates which can have this predicate as
        // positive/negative
        // effect
        if (idxArg == allPossibleValuesForEachArgOfThisPredicate.size()) {

            // Create the ground predicate
            String groundPredicate = "FLUENT_" + namePredicate + "_";
            for (int i = 0; i < valueTakenByEachArgsOfPredicate.size(); i++) {
                groundPredicate += valueTakenByEachArgsOfPredicate.get(i);
                if (i < valueTakenByEachArgsOfPredicate.size() - 1) {
                    groundPredicate += "_";
                }
            }

            // Add this predicate to the set of predicates which can have this predicate as
            // positive/negative effect
            if (predicateIsPositive) {
                if (this.dictGroundPredToLiftedActionWithGroundPredAsPosEff.containsKey(groundPredicate)) {
                    this.dictGroundPredToLiftedActionWithGroundPredAsPosEff.get(groundPredicate).add(nameLiftedAction);
                }

            } else {
                if (this.dictGroundPredToLiftedActionWithGroundPredAsNegEff.containsKey(groundPredicate)) {
                    this.dictGroundPredToLiftedActionWithGroundPredAsNegEff.get(groundPredicate).add(nameLiftedAction);
                }
            }

        } else {

            // Iterate over all the possible values of the current argument
            for (String value : allPossibleValuesForEachArgOfThisPredicate.get(idxArg)) {
                valueTakenByEachArgsOfPredicate.add(value);
                recursiveGroundPredicateToAllPositibleValues(nameLiftedAction, namePredicate,
                        allPossibleValuesForEachArgOfThisPredicate, valueTakenByEachArgsOfPredicate, idxArg + 1,
                        predicateIsPositive);
                valueTakenByEachArgsOfPredicate.remove(valueTakenByEachArgsOfPredicate.size() - 1);
            }
        }
    }

    /**
     * Compute all the parents name type and children name type of each type. Fill
     * the two map dictTypeToParentTypes and dictTypeToChildTypes
     */
    public void preprocessingComputeAllParentsAndChildrenEachTypes() {

        // Initialize our 2 maps + create A map from the name of the type to the object
        Map<String, TypedSymbol<String>> dictTypeNameToObj = new HashMap<>();
        this.dictTypeToParentTypes = new HashMap<>();
        this.dictTypeToChildTypes = new HashMap<>();

        for (TypedSymbol<String> typeObj : this.problem.getParsedProblem().getTypes()) {
            String typeName = typeObj.getValue();
            this.dictTypeToParentTypes.put(typeName, new HashSet<String>());
            this.dictTypeToChildTypes.put(typeName, new HashSet<String>());
            dictTypeNameToObj.put(typeName, typeObj);
        }

        // Now iterate over each object to set their parent. And once we have
        // them, reiterate to find all the children
        // Not optimal, but we do not care, as there are never too much different
        // objects

        for (TypedSymbol<String> type : this.problem.getParsedProblem().getTypes()) {
            recursiveFindAllParentOfType(this.dictTypeToParentTypes.get(type.getValue()), type, dictTypeNameToObj);
        }

        // Now, that we have all the parents of each type, we can compute the children
        for (String typeParent : this.dictTypeToParentTypes.keySet()) {
            for (String typeChild : this.dictTypeToParentTypes.keySet()) {
                if (this.dictTypeToParentTypes.get(typeChild).contains(typeParent)) {
                    this.dictTypeToChildTypes.get(typeParent).add(typeChild);
                }
            }
        }
    }

    public static void recursiveFindAllParentOfType(HashSet<String> parents, TypedSymbol<String> type,
            Map<String, TypedSymbol<String>> dictTypeNameToObj) {

        // If this type has no parent, do nothing
        if (type.getTypes().size() == 0) {
            return;
        }

        for (Symbol<String> nameTypeParent : type.getTypes()) {

            // Add the parent to the list
            parents.add(nameTypeParent.getValue());

            // Find the parent of this parent
            recursiveFindAllParentOfType(parents, dictTypeNameToObj.get(nameTypeParent.getValue()), dictTypeNameToObj);
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
    public String prettyDisplayMethod(Method m, Problem problem) {
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

    private String getSMTNameFluent(Fluent f, int layer, int position, Problem problem) {
        StringBuilder fluentToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        fluentToDisplay.append("(select FLUENT_" + problem.getPredicateSymbols().get(f.getSymbol()) + " (tuple ");

        // Then, for each argument of this fluent, add the argument into the string
        for (int fluentArg : f.getArguments()) {
            fluentToDisplay.append(problem.getConstantSymbols().get(fluentArg) + " ");
        }
        fluentToDisplay.append(layer + " " + position + "))");

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

    public String addLayerAndPos(String varToAdd, int layer, int pos) {
        return varToAdd + "__" + Integer.toString(layer) + "_" + Integer.toString(pos);
    }

    /**
     * # represent the layer and @ represention the position in the layer
     * 
     * @param fluentOrAction
     * @return
     */

    private String getBlankAction() {
        return "ACTION-Blank";
    }

    public String getCliqueAction() {
        return "CLIQUE_ACTION";
    }

    public String getCliqueMethod() {
        return "CLIQUE_METHOD";
    }

    private String getPrimitivePredicate() {
        return "Primitive";
    }

    private boolean fluentIsInClique(int idxFluent) {
        return this.dictFluentIdxToCliqueIdx.keySet().contains(idxFluent);
        // for (Collection<Integer> clique : this.treerex_cliques) {
        // if (clique.contains(idxFluent)) {
        // return true;
        // }
        // }
        // return false;
    }

    /**
     * Reduction initial task network
     * 
     * @return
     */
    private String rule1_reduc_init_task_network() {

        StringBuilder rule1 = new StringBuilder();

        for (int i = 0; i < this.problem.getInitialTaskNetwork().getTasks().size(); i++) {
            LayerElement layerElm = this.layers.get(0).layerElements.get(i);

            int idxTaskNetwork = this.problem.getInitialTaskNetwork().getTasks().get(i);

            // Get all the methods which can resolve this task and the scope of the variable
            // of each of the method which can resolve this task
            Map<String, LiftedMethod> methodNameToLiftedMethod = new HashMap<>();

            for (int idxMethod : this.problem.getTaskResolvers().get(idxTaskNetwork)) {
                Method m = this.problem.getMethods().get(idxMethod);

                if (!methodNameToLiftedMethod.containsKey(m.getName())) {

                    // Create our lifted method object
                    // Get the parsed method associated with this method
                    for (ParsedMethod parsedMethod : this.problem.getParsedProblem().getMethods()) {
                        if (parsedMethod.getName().getValue().equals(m.getName())) {
                            LiftedMethod liftedMethod = convertParsedMethodIntoLiftedMethod(parsedMethod, null, 0, i);
                            // Clear all the scope of the method since we will fill it with the initial
                            // values
                            for (ScopeVariable argMethod : liftedMethod.getParameters()) {
                                argMethod.getPossibleValueVariable().clear();
                            }
                            methodNameToLiftedMethod.put(m.getName(), liftedMethod);
                            break;
                        }
                    }
                }
                // Add all the arguments in the scope of the method
                LiftedMethod liftedMethod = methodNameToLiftedMethod.get(m.getName());
                for (int argi = 0; argi < m.getParameters().length; argi++) {
                    String objName = problem.getConstantSymbols().get(m.getInstantiations()[argi]);
                    liftedMethod.getParameters().get(argi).addValueToScope(objName);
                }
                this.allScopeVariables.addAll(liftedMethod.getParameters());
            }

            // Now we can add all of our initial methods with the appropriate scope
            rule1.append("(assert (or ");
            for (String methodName : methodNameToLiftedMethod.keySet()) {

                String methodNameWithLayer = methodNameToLiftedMethod.get(methodName).getUniqueName();
                // Now, we can add it to our variable with the scope of the variablze
                // here...
                rule1.append(methodNameWithLayer + " ");
                // TODO SEE LATER
                // layerElm.addLiftedReductionWithScope(methodName,
                // methodNameToScope.get(methodName));
                layerElm.addLiftedReduction(methodNameToLiftedMethod.get(methodName));
                addToAllVariables(methodNameWithLayer);
            }

            rule1.append("))\n");
        }

        return rule1.toString();
    }

    private LiftedMethod convertParsedMethodIntoLiftedMethod(ParsedMethod method, LiftedMethod parentLiftedMethod,
            int layer, int layerElement) {
        LiftedMethod liftedMethod = new LiftedMethod(method.getName().getValue(), parentLiftedMethod, layer,
                layerElement);

        // Create all the parameters of the lifted method
        for (int i = 0; i < method.getParameters().size(); i++) {

            // Get the type of the parameter
            String type = method.getParameters().get(i).getTypes().get(0).getValue();

            // Get all the possible values of the parameter
            HashSet<String> possibleValues = new HashSet<>();
            possibleValues.addAll(this.dictTypeToObjects.get(type));
            for (String childType : this.dictTypeToChildTypes.get(type)) {
                possibleValues.addAll(this.dictTypeToObjects.get(childType));
            }

            ScopeVariable param = new ScopeVariable();
            param.setType(type);
            param.getPossibleValueVariable().addAll(possibleValues);

            liftedMethod.addParameter(param);
        }

        // Create the precondition of the lifted method
        liftedMethod.addPreconditionsFromParsedMethodPreconditions(method.getPreconditions());

        return liftedMethod;
    }

    /**
     * Add the initial state constrains
     * 
     * @return
     */
    private String rule2_declaration_init_facts() {

        StringBuilder rule2 = new StringBuilder();

        String var;

        // Compute first the initials facts for the SAS+ fluents
        // if (this.optimizationsToUse.useSASplus) {
        // for (List<Integer> clique : this.treerex_cliques) {

        // // Check for the fluent which is true among all fluents in the clique
        // // there should be only one
        // for (Integer idxFluent : clique) {
        // if (this.problem.getInitialState().getPositiveFluents().get(idxFluent)) {
        // Fluent f = this.problem.getFluents().get(idxFluent);
        // // var = addLayerAndPos(prettyDisplayCliqueFluent(f, problem), 0, 0);
        // var =
        // addLayerAndPos(prettyDisplayCliqueFluent(this.treerex_cliques.indexOf(clique),
        // problem),
        // 0, 0);
        // addToAllVariables(var);
        // this.layers.get(0).layerElements.get(0).addClique(clique, 0, 0);
        // constrainsInitState
        // .append("(assert (= " +
        // var
        // + " " + clique.indexOf(idxFluent) + "))\n");
        // }
        // }
        // }
        // }

        for (int i = 0; i < this.factsSize; i++) {
            Fluent f = this.problem.getFluents().get(i);
            if (!this.optimizationsToUse.useSASplus || !fluentIsInClique(i)) {
                var = addLayerAndPos(prettyDisplayFluent(f, problem), 0, 0);
                addToAllVariables(var);

                String nameFluent = problem.getPredicateSymbols().get(f.getSymbol());
                if (this.staticPredicates.contains(nameFluent)) {
                    if (!this.dictStaticPredicateNameToAllFluentWithThisPredicate.containsKey(nameFluent)) {
                        this.dictStaticPredicateNameToAllFluentWithThisPredicate.put(nameFluent, new HashSet<>());
                    }
                    this.dictStaticPredicateNameToAllFluentWithThisPredicate.get(nameFluent).add(f);
                }

                if (this.problem.getInitialState().getPositiveFluents().get(i)) {

                    rule2
                            .append("(assert (= " +
                                    var
                                    + " true))\n");

                    this.layers.get(0).layerElements.get(0).addPositiveFluent(f);
                } else {

                    rule2
                            .append("(assert (= "
                                    + var
                                    + " false))\n");

                    this.layers.get(0).layerElements.get(0).addNegativeFluent(f);
                }
            }
        }

        return rule2.toString();
    }

    private String rule3_action_is_prim_reduct_in_not_prim(int layer, int layerElm) {
        StringBuilder rule3 = new StringBuilder();

        LayerElement layerElement = this.layers.get(layer).layerElements.get(layerElm);
        String varPrimLayerElm = addLayerAndPos(getPrimitivePredicate(), layer, layerElm);

        addToAllVariables(varPrimLayerElm);

        for (LiftedMethod liftedMethod : layerElement.getLiftedReductions()) {
            rule3.append("(assert (=> " + liftedMethod.getUniqueName() + " (not "
                    + varPrimLayerElm + ")))\n");
        }
        for (LiftedAction liftedAction : layerElement.getLiftedActions()) {
            rule3.append(
                    "(assert (=> " + liftedAction.getUniqueName() + " " + varPrimLayerElm + "))\n");
        }

        if (layerElement.canContainsBlankAction()) {
            String varBlankAction = addLayerAndPos(getBlankAction(), layer, layerElm);
            addToAllVariables(varBlankAction);
            rule3.append("(assert (=> " + varBlankAction + " "
                    + varPrimLayerElm + "))\n");
        }
        return rule3.toString();
    }

    private String rule4_at_most_one_action_and_reduction(int layer, int layerElm) {

        StringBuilder rule4 = new StringBuilder();

        LayerElement layerElement = this.layers.get(layer).layerElements.get(layerElm);

        LiftedMethod[] allLiftedReductions = layerElement.getLiftedReductions().toArray(new LiftedMethod[0]);

        for (int i = 0; i < allLiftedReductions.length; i++) {
            for (int j = i + 1; j < allLiftedReductions.length; j++) {
                rule4.append("(assert (or (not " + allLiftedReductions[i].getUniqueName()
                        + ") (not " + allLiftedReductions[j].getUniqueName() + ")))\n");
            }
        }

        LiftedAction[] allLiftedActions = layerElement.getLiftedActions().toArray(new LiftedAction[0]);
        for (int i = 0; i < allLiftedActions.length; i++) {
            String a1 = allLiftedActions[i].getUniqueName();
            for (int j = i + 1; j < allLiftedActions.length; j++) {
                String a2 = allLiftedActions[j].getUniqueName();
                rule4.append("(assert (or (not " + a1 + ") (not " + a2 + ")))\n");
            }
            // Add the blank action as well if this elm can contain a blank action
            if (layerElement.canContainsBlankAction()) {
                String varBlankAction = addLayerAndPos(getBlankAction(), layer, layerElm);
                rule4.append("(assert (or (not " + a1 + ") (not " + varBlankAction + ")))\n");
            }
        }

        return rule4.toString();
    }

    private String rule5_operation_implies_preconditions(int layer, int layerElm) {

        StringBuilder rule5 = new StringBuilder();

        LayerElement layerElement = this.layers.get(layer).layerElements.get(layerElm);

        for (LiftedMethod liftedMethod : layerElement.getLiftedReductions()) {
            for (PseudoFact liftedPrecondition : liftedMethod.getPreconditions()) {
                rule5.append("(assert (=> " + liftedMethod.getUniqueName() + " ");
                if (!liftedPrecondition.isPositive()) {
                    rule5.append("(not ");
                }
                if (liftedPrecondition.getPredicateName().equals("=")) {
                    rule5.append("(or ");
                    // Get the intersection of the two scopeVariables
                    ScopeVariable scopeVar1 = liftedPrecondition.getScopeVariables().get(0);
                    ScopeVariable scopeVar2 = liftedPrecondition.getScopeVariables().get(1);
                    HashSet<String> intersection = new HashSet<String>(scopeVar1.getPossibleValueVariable());
                    intersection.retainAll(scopeVar2.getPossibleValueVariable());
                    for (String var : intersection) {
                        rule5.append("(and " + scopeVar1.getUniqueName() + "_" + var + " " + scopeVar2.getUniqueName()
                                + "_" + var + ") ");
                    }
                    rule5.append(")");
                } else {
                    String var = liftedPrecondition.getUniqueName();
                    rule5.append(var);
                    addToAllVariables(var);
                }

                if (!liftedPrecondition.isPositive()) {
                    rule5.append(")");
                }
                rule5.append("))\n");

                layerElement.addPseudoFact(liftedPrecondition);
            }
        }

        for (LiftedAction liftedAction : layerElement.getLiftedActions()) {
            for (PseudoFact liftedPrecondition : liftedAction.getPreconditions()) {
                rule5.append("(assert (=> " + liftedAction.getUniqueName() + " ");
                if (!liftedPrecondition.isPositive()) {
                    rule5.append("(not ");
                }
                String var = liftedPrecondition.getUniqueName();
                rule5.append(var);
                if (!liftedPrecondition.isPositive()) {
                    rule5.append(")");
                }
                rule5.append("))\n");
                addToAllVariables(var);
                layerElement.addPseudoFact(liftedPrecondition);
            }
        }
        return rule5.toString();
    }

    private String rule6_action_implies_effects(int layer, int layerElm) {

        StringBuilder rule6 = new StringBuilder();

        LayerElement layerElement = this.layers.get(layer).layerElements.get(layerElm);

        for (LiftedAction liftedAction : layerElement.getLiftedActions()) {
            for (PseudoFact liftedEffect : liftedAction.getEffects()) {
                rule6.append("(assert (=> " + liftedAction.getUniqueName() + " ");
                if (!liftedEffect.isPositive()) {
                    rule6.append("(not ");
                }
                String var = liftedEffect.getUniqueName();
                rule6.append(var);
                if (!liftedEffect.isPositive()) {
                    rule6.append(")");
                }
                rule6.append("))\n");

                addToAllVariables(var);
                this.layers.get(layer).layerElements.get(layerElm + 1).addPseudoFact(liftedEffect);
            }
        }
        return rule6.toString();
    }

    private String rule_7_transitionnal_ground_fact(int layer, int layerElm) {
        StringBuilder rule7 = new StringBuilder();

        // Get the successor of this layer element
        int childLayerElm = this.layers.get(layer).n.get(layerElm);

        for (Fluent groundFact : this.problem.getFluents()) {

            // Skip static predicates (as they will never change)
            if (this.staticPredicates.contains(problem.getPredicateSymbols().get(groundFact.getSymbol()))) {
                continue;
            }
            // for (Fluent groundFact :
            // this.layers.get(layer).layerElements.get(layerElm).getPositivesFluents()) {
            String varFluent = addLayerAndPos(prettyDisplayFluent(groundFact, problem), layer, layerElm);
            String varFluentInChildLayer = addLayerAndPos(prettyDisplayFluent(groundFact, problem), layer + 1,
                    childLayerElm);
            addToAllVariables(varFluentInChildLayer);
            // this.layers.get(layer +
            // 1).layerElements.get(childLayerElm).addPositiveFluent(groundFact);
            rule7.append("(assert (= " + varFluent + " " + varFluentInChildLayer + "))\n");
        }

        if (this.layers.get(layer).layerElements.get(layerElm).canContainsBlankAction()) {
            this.layers.get(layer + 1).layerElements.get(childLayerElm).addBlankAction();
            ;
        }

        return rule7.toString();
    }

    private String rule_8_transitionnal_operators(int layer, int layerElm) {
        StringBuilder rule8 = new StringBuilder();

        int maxChildElmsForLayerElm = this.layers.get(layer).e.get(layerElm);

        int childLayerElm = this.layers.get(layer).n.get(layerElm);

        HashSet<LiftedMethod> methodAvailableForThisLayerElm = this.layers.get(layer).layerElements.get(layerElm)
                .getLiftedReductions();

        // First, describe the transitionnal methods
        for (LiftedMethod liftedMethod : methodAvailableForThisLayerElm) {

            // Get the parseMethod object associated with this method
            ParsedMethod method = this.methodNameToObj.get(liftedMethod.getName());

            int numberSubtasksMethod = method.getSubTasks().getChildren().size();

            // Iterate over all subtasks of this method
            for (int idxSubtask = 0; idxSubtask < numberSubtasksMethod; idxSubtask++) {

                rule8.append("(assert (=> " + liftedMethod.getUniqueName() + " ");

                Expression<String> subtask = method.getSubTasks().getChildren().get(idxSubtask);

                // Check if the subtasks is an action (primitive task or another task)

                String subtaskName = subtask.getSymbol().getValue();

                if (this.actionNameToObj.keySet().contains(subtaskName)) {
                    // This is an action. Get the action object associated with this
                    // Initialize the action with the correct scope

                    LiftedAction liftedAction = new LiftedAction(subtaskName, liftedMethod, layer + 1,
                            childLayerElm + idxSubtask);

                    // Find the scope of the action
                    for (int argi = 0; argi < subtask.getArguments().size(); argi++) {
                        String nameArg = subtask.getArguments().get(argi).getValue();
                        try {
                            int idxArgOfMethod = Integer.parseInt(nameArg.substring(2));
                            liftedAction.getParameters().add(liftedMethod.getParameters().get(idxArgOfMethod));
                        } catch (Exception e) {
                            // Maybe it is a constant variable
                            // scopeAction.add(nameArg);
                            System.out.println("WE WILL SEE THAT LATER...");
                            System.exit(1);
                        }
                    }

                    // We need to find the parsed action associated with this lifted action
                    for (ParsedAction parsedAction : this.problem.getParsedProblem().getActions()) {
                        if (parsedAction.getName().getValue().equals(liftedAction.getName())) {
                            liftedAction.addPreconditionsFromParsedActionPreconditions(parsedAction.getPreconditions());
                            liftedAction.addEffectsFromParsedActionEffects(parsedAction.getEffects());
                            this.allLiftedActionsLastLayer.add(liftedAction);

                            this.allScopeVariables.addAll(liftedAction.getParameters());
                            break;
                        }
                    }

                    // Add the action in the child layer
                    this.layers.get(layer + 1).layerElements.get(childLayerElm + idxSubtask)
                            .addLiftedAction(liftedAction);

                    String actionNameInLayerPosition = liftedAction.getUniqueName();
                    addToAllVariables(actionNameInLayerPosition);

                    rule8.append(actionNameInLayerPosition + "))\n");
                } else {

                    // First, we need to know the scope of each argument of this subtask
                    ArrayList<ScopeVariable> scopeSubtask = new ArrayList<ScopeVariable>();
                    for (int argi = 0; argi < subtask.getArguments().size(); argi++) {
                        String nameArg = subtask.getArguments().get(argi).getValue();
                        try {
                            int idxArgOfMethod = Integer.parseInt(nameArg.substring(2));
                            scopeSubtask.add(liftedMethod.getParameters().get(idxArgOfMethod));
                        } catch (Exception e) {
                            // Maybe it is a constant variable
                            // scopeSubtask.add(nameArg);
                            System.out.println("WE WILL SEE THAT LATER...");
                            System.exit(1);
                        }
                    }

                    rule8.append("(or ");

                    // Now, we need to find all the methods which can solve this subtask
                    for (ParsedMethod subMethod : problem.getParsedProblem().getMethods()) {

                        String subMethodName = subMethod.getName().getValue();
                        // ArrayList<ScopeVariable> scopeSubMethod = new ArrayList<ScopeVariable>();

                        // If this method cannot resolve this subtask, continue
                        if (!subMethod.getTask().getSymbol().getValue().equals(subtaskName)) {
                            continue;
                        }

                        // Create our new submethod
                        LiftedMethod liftedSubMethod = new LiftedMethod(subMethodName, liftedMethod, layer + 1,
                                childLayerElm + idxSubtask);

                        // Here it where it is delicate, when this method use a parameter of the task
                        // parent, use the scope of the task
                        // parent. Else, initialize a new scope with all possible value in it (maybe it
                        // is not optimal, I don't know there)

                        // First, we need to know with which argument the parent method called the task

                        // Iterate over all argument of the subMethod
                        for (TypedSymbol<String> subMethodArg : subMethod.getParameters()) {
                            // Find if this is also a parameter of the parent task
                            String nameParameter = subMethodArg.getValue();
                            // int idxArgOfMethod = Integer.parseInt(nameParameter.substring(2));

                            // Check if it is a parameter of the parent task
                            boolean isParameterOfParentTask = false;
                            for (int i_parentTaskParam = 0; i_parentTaskParam < subMethod.getTask().getArguments()
                                    .size(); i_parentTaskParam++) {
                                if (subMethod.getTask().getArguments().get(i_parentTaskParam).getValue()
                                        .equals(nameParameter)) {
                                    // Use the scope of the parent task
                                    liftedSubMethod.getParameters().add(scopeSubtask.get(i_parentTaskParam));
                                    isParameterOfParentTask = true;
                                    break;
                                }
                            }

                            // Or if it is a new parameter introduced by the method
                            if (!isParameterOfParentTask) {
                                ScopeVariable scopeArg = new ScopeVariable();
                                this.allScopeVariables.add(scopeArg);
                                // Get the type of the argument
                                String typeArg = subMethodArg.getTypes().get(0).getValue();
                                // Initialize the scope argument with all value of this type
                                scopeArg.addTypeVariable(typeArg);
                                scopeArg.getPossibleValueVariable().addAll(dictTypeToObjects.get(typeArg));
                                for (String childType : this.dictTypeToChildTypes.get(typeArg)) {
                                    scopeArg.getPossibleValueVariable().addAll(dictTypeToObjects.get(childType));
                                }

                                liftedSubMethod.getParameters().add(scopeArg);
                            }
                        }

                        // Can only be called after the scope of the method is initialized
                        liftedSubMethod.addPreconditionsFromParsedMethodPreconditions(subMethod.getPreconditions());
                        String liftedSubMethodNameLayerElement = liftedSubMethod.getUniqueName();
                        addToAllVariables(liftedSubMethodNameLayerElement);

                        rule8.append(liftedSubMethodNameLayerElement + " ");

                        this.layers.get(layer + 1).layerElements.get(childLayerElm + idxSubtask)
                                .addLiftedReduction(liftedSubMethod);
                        this.allScopeVariables.addAll(liftedSubMethod.getParameters());
                    }
                    rule8.append(")))\n");
                }
            }

            if (numberSubtasksMethod == 0) {
                // Create a speial noop action for this case
                LiftedAction noopAction = new LiftedAction(true, liftedMethod, layer + 1, childLayerElm);
                String fullNameNoopAction = noopAction.getUniqueName();
                rule8.append("(assert (=> " + liftedMethod.getUniqueName() + " " + fullNameNoopAction
                        + "))\n");
                addToAllVariables(fullNameNoopAction);
                this.layers.get(layer + 1).layerElements.get(childLayerElm).addLiftedAction(noopAction);
                this.allLiftedActionsLastLayer.add(noopAction);
                numberSubtasksMethod = 1;
            }

            for (int i = numberSubtasksMethod; i < maxChildElmsForLayerElm; i++) {

                String varBlankAction = addLayerAndPos(getBlankAction(), layer + 1, childLayerElm + i);
                addToAllVariables(varBlankAction);
                rule8.append("(assert (=> " + liftedMethod.getUniqueName() + " " + varBlankAction
                        + "))\n");

                // Add as well the blank action to our layer
                this.layers.get(layer + 1).layerElements.get(childLayerElm + i).addBlankAction();
            }
        }

        // We also need to propagate actions from the parent layer to the child layer
        HashSet<LiftedAction> actionsAvailableForThisLayerElm = this.layers.get(layer).layerElements.get(layerElm)
                .getLiftedActions();

        for (LiftedAction liftedAction : actionsAvailableForThisLayerElm) {

            LiftedAction childLiftedAction = new LiftedAction(liftedAction);
            childLiftedAction.setLayer(layer + 1);
            childLiftedAction.setLayerElement(childLayerElm);

            this.allLiftedActionsLastLayer.add(childLiftedAction);
            // Add the same lifted action in the child layer
            this.layers.get(layer + 1).layerElements.get(childLayerElm).addLiftedAction(childLiftedAction);

            // Also add it to the variables
            String varActionNextLayer = childLiftedAction.getUniqueName();
            addToAllVariables(varActionNextLayer);
            rule8.append("(assert (= " + liftedAction.getUniqueName() + " " + varActionNextLayer
                    + "))\n");

            // But we also need to indicate blank action for the other elements of the child
            for (int i = 1; i < maxChildElmsForLayerElm; i++) {
                String varBlankAction = addLayerAndPos(getBlankAction(), layer + 1, childLayerElm + i);
                addToAllVariables(varBlankAction);
                rule8.append("(assert (=> " + liftedAction.getUniqueName() + " " + varBlankAction
                        + "))\n");

                // Add as well the blank action to our layer
                this.layers.get(layer + 1).layerElements.get(childLayerElm + i).addBlankAction();
            }
        }

        return rule8.toString();
    }

    private String rule10_layer_is_fully_primitive(int layer) {
        StringBuilder rule16 = new StringBuilder();
        int numberElementsInLayer = this.layers.get(layer).layerElements.size();
        rule16.append("(assert (and ");
        for (int idxElmLayer = 0; idxElmLayer < numberElementsInLayer; idxElmLayer++) {
            String varPrimitivePredicate = addLayerAndPos(getPrimitivePredicate(), layer, idxElmLayer);
            addToAllVariables(varPrimitivePredicate);
            rule16.append(varPrimitivePredicate + " ");
        }
        rule16.append("))\n");
        return rule16.toString();
    }

    private String rule11_scope_var_can_take_at_most_one_value() {
        StringBuilder rule11 = new StringBuilder();
        for (ScopeVariable scopeVar : this.allScopeVariables) {
            if (this.scopeVariablesAlreadyDeclared.contains(scopeVar)) {
                continue;
            }
            String[] scopeVarValues = scopeVar.getPossibleValueVariable().toArray(new String[0]);
            if (scopeVarValues.length > 1) {
                rule11.append("(assert (and ");
                for (int i = 0; i < scopeVarValues.length; i++) {
                    for (int j = i + 1; j < scopeVarValues.length; j++) {
                        String nameScopeVarValue1 = scopeVar.getUniqueName() + "_" + scopeVarValues[i];
                        String nameScopeVarValue2 = scopeVar.getUniqueName() + "_" + scopeVarValues[j];
                        addToAllVariables(nameScopeVarValue1);
                        addToAllVariables(nameScopeVarValue2);
                        rule11.append("(or (not " + nameScopeVarValue1 + ") (not " + nameScopeVarValue2 + ")) ");
                    }
                }
                rule11.append("))\n");
                scopeVariablesAlreadyDeclared.add(scopeVar);
            }
        }
        return rule11.toString();
    }

    private String rule12_operator_true_implies_scope_var_at_least_one_value(int layer, int layerElm) {

        StringBuilder rule18 = new StringBuilder();

        // First, do it for the methods of the layer element
        for (LiftedMethod liftedMethod : this.layers.get(layer).layerElements.get(layerElm).getLiftedReductions()) {
            for (ScopeVariable paramMethod : liftedMethod.getParameters()) {
                if (paramMethod.isConstant()) {
                    continue;
                }
                rule18.append("(assert (=> " + liftedMethod.getUniqueName() + " (or ");
                for (String valuePossible : paramMethod.getPossibleValueVariable()) {
                    rule18.append(paramMethod.getUniqueName() + "_" + valuePossible + " ");
                }
                rule18.append(")))\n");
            }
        }

        // Do the same for the action possible for this layer element
        for (LiftedAction liftedAction : this.layers.get(layer).layerElements.get(layerElm).getLiftedActions()) {
            for (ScopeVariable paramMethod : liftedAction.getParameters()) {
                if (paramMethod.isConstant()) {
                    continue;
                }
                rule18.append("(assert (=> " + liftedAction.getUniqueName() + " (or ");
                for (String valuePossible : paramMethod.getPossibleValueVariable()) {
                    rule18.append(paramMethod.getUniqueName() + "_" + valuePossible + " ");
                }
                rule18.append(")))\n");
            }
        }

        return rule18.toString();
    }

    private String rule13_substituing_pseudo_fact_to_ground_fact(int layer, int layerElm) {
        StringBuilder rule13 = new StringBuilder();

        LayerElement layerElement = this.layers.get(layer).layerElements.get(layerElm);

        for (PseudoFact pseudoFact : layerElement.getPseudoFacts()) {
            if (pseudoFact.getPredicateName().equals("=")) {
                continue;
            }

            if (pseudoFact.isGroundFact()) {
                continue;
            }

            // If the pseudo fact is a static predicate, we use the rule 22 (TODO implement
            // rule 23 when it result in better encoding)
            if (this.staticPredicates.contains(pseudoFact.getPredicateName())) {
                // We need to get all the value that this static predicate can take
                rule13.append("(assert (=> " + pseudoFact.getUniqueName() + " (or ");
                for (Fluent f : this.dictStaticPredicateNameToAllFluentWithThisPredicate
                        .get(pseudoFact.getPredicateName())) {
                    StringBuilder temp = new StringBuilder();
                    boolean canUnify = true;
                    temp.append("(and ");
                    for (int i = 0; i < f.getArguments().length; i++) {
                        String nameGroundParamter = problem.getConstantSymbols().get(f.getArguments()[i]);
                        if (pseudoFact.getScopeVariables().get(i).isConstant()) {
                            // Two cases here, either the constant is the same as the one in the pseudo
                            // fact, or it is not
                            if (pseudoFact.getScopeVariables().get(i).getUniqueName().equals(nameGroundParamter)) {
                                // This paramter is invariant true
                                continue;
                            } else {
                                // We can stop here for this ground fact as we cannot unify with it
                                canUnify = false;
                                break;
                            }
                        }
                        if (pseudoFact.getScopeVariables().get(i).getPossibleValueVariable()
                                .contains(nameGroundParamter)) {
                            temp.append(pseudoFact.getScopeVariables().get(i).getUniqueName() + "_" + nameGroundParamter
                                    + " ");
                        } else {
                            // We can stop here for this ground fact as we cannot unify with it
                            canUnify = false;
                            break;
                        }
                    }
                    if (canUnify) {
                        temp.append(")");
                        rule13.append(temp.toString() + " ");
                    }
                }
                rule13.append(")))\n");
            } else {
                recursiveGenerateAllSubstituingPseudoFactToGroundFact(layer, layerElm, pseudoFact,
                        new ArrayList<String>(),
                        rule13);
            }

        }

        return rule13.toString();
    }

    public void recursiveGenerateAllSubstituingPseudoFactToGroundFact(int layer, int layerElm, PseudoFact pseudoFact,
            ArrayList<String> valuesTakenByEachArg, StringBuilder rule13) {

        if (valuesTakenByEachArg.size() == pseudoFact.getScopeVariables().size()) {
            // We have a complete substitution, we can now write the rule
            StringBuilder varGroundFact = new StringBuilder();
            varGroundFact.append(pseudoFact.getPredicateName());
            for (String valueTaken : valuesTakenByEachArg) {
                varGroundFact.append("_" + valueTaken);
            }

            rule13.append("(assert (=> (and ");
            for (int i = 0; i < pseudoFact.getScopeVariables().size(); i++) {
                if (!pseudoFact.getScopeVariables().get(i).isConstant()) {
                    String scopeVarName = pseudoFact.getScopeVariables().get(i).getUniqueName();
                    String valueTaken = valuesTakenByEachArg.get(i);
                    rule13.append(scopeVarName + "_" + valueTaken + " ");
                }
            }
            rule13.append(") (= " + pseudoFact.getUniqueName() + " FLUENT_"
                    + addLayerAndPos(varGroundFact.toString(), layer, layerElm) + ")))\n");
            return;
        } else {
            ScopeVariable scopeVar = pseudoFact.getScopeVariables().get(valuesTakenByEachArg.size());
            for (String valuePossible : scopeVar.getPossibleValueVariable()) {
                ArrayList<String> newValuesTakenByEachArg = new ArrayList<>(valuesTakenByEachArg);
                newValuesTakenByEachArg.add(valuePossible);
                recursiveGenerateAllSubstituingPseudoFactToGroundFact(layer, layerElm, pseudoFact,
                        newValuesTakenByEachArg, rule13);
            }
        }
    }

    private boolean groundFactCanBeUnifiedWithPseudoFacts(Fluent groundFact, ArrayList<PseudoFact> pseudoFacts,
            boolean checkPositivePredicate) {

        String namePredicate = problem.getPredicateSymbols().get(groundFact.getSymbol());

        boolean canBeUnified = false;
        for (PseudoFact pseudoFact : pseudoFacts) {

            if (!pseudoFact.getPredicateName().equals(namePredicate)
                    || (checkPositivePredicate && !pseudoFact.isPositive())
                    || (!checkPositivePredicate && pseudoFact.isPositive())) {
                canBeUnified = false;
                continue;
            }

            canBeUnified = true;

            for (int argi = 0; argi < pseudoFact.getScopeVariables().size(); argi++) {

                // Get the contstaint parameter of the ground fact
                String groundParam = problem.getConstantSymbols().get(groundFact.getArguments()[argi]);

                // Check if the lifted action can have this parameter
                if (!((pseudoFact.getScopeVariables().get(argi).isConstant()
                        && pseudoFact.getScopeVariables().get(argi).getUniqueName().equals(groundParam))
                        || pseudoFact.getScopeVariables().get(argi).getPossibleValueVariable().contains(groundParam))) {
                    canBeUnified = false;
                    break;
                }
            }
            if (canBeUnified) {
                return true;
            }
        }
        return false;
    }

    private String rule14_frame_axioms(int layer, int layerElm) {
        StringBuilder rule14 = new StringBuilder();

        String primitivePredicate = addLayerAndPos(getPrimitivePredicate(), layer, layerElm);
        addToAllVariables(primitivePredicate);

        HashSet<String> actionNameAvailableForThisLayerElement = new HashSet<String>();
        for (LiftedAction liftedAction : this.layers.get(layer).layerElements.get(layerElm).getLiftedActions()) {
            actionNameAvailableForThisLayerElement.add(liftedAction.getName());
        }

        // For now, do the frame axioms with all the ground facts at each layer element
        for (Fluent f : this.problem.getFluents()) {

            // Skip the static predicates (as they will never change)
            if (this.staticPredicates.contains(problem.getPredicateSymbols().get(f.getSymbol()))) {
                continue;
            }

            String nameFluent = prettyDisplayFluent(f, problem);

            if (nameFluent.equals("FLUENT_free_right") && layer == 1 && layerElm == 5) {
                System.out.println("debug");
            }

            HashSet<String> interNeg = new HashSet<String>(
                    this.dictGroundPredToLiftedActionWithGroundPredAsNegEff.get(nameFluent));
            interNeg.retainAll(actionNameAvailableForThisLayerElement);

            HashSet<LiftedAction> interNegObj = new HashSet<LiftedAction>();

            if (nameFluent.equals("FLUENT_at_truck_0_city_loc_0") && layer == 4 && layerElm == 5) {
                System.out.println("debug");
            }

            // Check if the ground fact can be unified with one of the effects of the lifted
            // actions
            for (LiftedAction liftedAction : this.layers.get(layer).layerElements.get(layerElm).getLiftedActions()) {
                if (!interNeg.contains(liftedAction.getName())) {
                    continue;
                }
                if (groundFactCanBeUnifiedWithPseudoFacts(f, liftedAction.getEffects(), false)) {
                    interNegObj.add(liftedAction);
                }
            }

            HashSet<String> interPos = new HashSet<String>(
                    this.dictGroundPredToLiftedActionWithGroundPredAsPosEff.get(nameFluent));
            interPos.retainAll(actionNameAvailableForThisLayerElement);

            HashSet<LiftedAction> interPosObj = new HashSet<LiftedAction>();

            // Check if the ground fact can be unified with one of the effects of the lifted
            // actions
            for (LiftedAction liftedAction : this.layers.get(layer).layerElements.get(layerElm).getLiftedActions()) {
                if (!interPos.contains(liftedAction.getName())) {
                    continue;
                }
                if (groundFactCanBeUnifiedWithPseudoFacts(f, liftedAction.getEffects(), true)) {
                    interPosObj.add(liftedAction);
                }
            }

            String fluentCurrentLayerElm = addLayerAndPos(nameFluent, layer, layerElm);
            String fluentNextLayerElm = addLayerAndPos(nameFluent, layer, layerElm + 1);
            addToAllVariables(fluentCurrentLayerElm);
            addToAllVariables(fluentNextLayerElm);
            rule14.append("(assert (=> (and " + fluentCurrentLayerElm + " (not " + fluentNextLayerElm + ")) (or (not "
                    + primitivePredicate + ") ");
            for (LiftedAction liftedAction : interNegObj) {
                rule14.append(liftedAction.getUniqueName() + " ");
            }
            rule14.append(")))\n");

            rule14.append("(assert (=> (and (not " + fluentCurrentLayerElm + ") " + fluentNextLayerElm + ") (or (not "
                    + primitivePredicate + ") ");
            for (LiftedAction liftedAction : interPosObj) {
                rule14.append(liftedAction.getUniqueName() + " ");
            }
            rule14.append(")))\n");
        }
        return rule14.toString();
    }

    private String rule15_predicate_change_implies_specific_grounding(int layer, int layerElm) {
        StringBuilder rule15 = new StringBuilder();

        HashSet<LiftedAction> liftedActionAvailableForThisLayerElement = this.layers.get(layer).layerElements
                .get(layerElm).getLiftedActions();

        // For now, do the frame axioms with all the ground facts at each layer element
        for (Fluent f : this.problem.getFluents()) {

            // Skip the static predicates (as they will never change)
            if (this.staticPredicates.contains(problem.getPredicateSymbols().get(f.getSymbol()))) {
                continue;
            }

            String namePredicate = problem.getPredicateSymbols().get(f.getSymbol());
            String nameFluent = prettyDisplayFluent(f, problem);
            String fluentCurrentLayerElm = addLayerAndPos(nameFluent, layer, layerElm);
            String fluentNextLayerElm = addLayerAndPos(nameFluent, layer, layerElm + 1);
            addToAllVariables(fluentCurrentLayerElm);
            addToAllVariables(fluentNextLayerElm);

            ArrayList<String> parametersGroundFact = new ArrayList<String>();
            for (int fluentArg : f.getArguments()) {
                parametersGroundFact.add(problem.getConstantSymbols().get(fluentArg));
            }

            HashSet<String> allLiftedActionsWithGroundPredAsNegEff = this.dictGroundPredToLiftedActionWithGroundPredAsNegEff
                    .get(nameFluent);

            // Get all the lifted actions available for this layer element that have this
            // ground predicate as a negative effect
            HashSet<LiftedAction> liftedActionsAvailableForThisLayerElmWithGroundPredAsNegEff = new HashSet<LiftedAction>();
            for (LiftedAction liftedAction : liftedActionAvailableForThisLayerElement) {
                if (allLiftedActionsWithGroundPredAsNegEff.contains(liftedAction.getName())
                        && groundFactCanBeUnifiedWithPseudoFacts(f, liftedAction.getEffects(), false)) {

                    liftedActionsAvailableForThisLayerElmWithGroundPredAsNegEff.add(liftedAction);
                }
            }

            if (liftedActionsAvailableForThisLayerElmWithGroundPredAsNegEff.size() > 0) {

                for (LiftedAction liftedAction : liftedActionsAvailableForThisLayerElmWithGroundPredAsNegEff) {
                    rule15.append("(assert (=> (and " + fluentCurrentLayerElm + " (not " + fluentNextLayerElm + ") "
                            + liftedAction.getUniqueName() + ") (or ");
                    for (PseudoFact effect : liftedAction.getEffects()) {
                        if (effect.isPositive() || !effect.getPredicateName().equals(namePredicate)) {
                            continue;
                        }
                        rule15.append("(and true ");
                        for (int argi = 0; argi < effect.getScopeVariables().size(); argi++) {
                            if (effect.getScopeVariables().get(argi).isConstant()) {
                                continue;
                            }
                            String paramLiftedAction = effect.getScopeVariables().get(argi).getUniqueName();
                            String groundName = parametersGroundFact.get(argi);
                            rule15.append(paramLiftedAction + "_" + groundName + " ");
                        }
                    }
                    rule15.append("))))\n");
                }
            }

            HashSet<String> allLiftedActionsWithGroundPredAsPosEff = this.dictGroundPredToLiftedActionWithGroundPredAsPosEff
                    .get(nameFluent);

            // Get all the lifted actions available for this layer element that have this
            // ground predicate as a negative effect
            HashSet<LiftedAction> liftedActionsAvailableForThisLayerElmWithGroundPredAsPosEff = new HashSet<LiftedAction>();
            for (LiftedAction liftedAction : liftedActionAvailableForThisLayerElement) {
                if (allLiftedActionsWithGroundPredAsPosEff.contains(liftedAction.getName())
                        && groundFactCanBeUnifiedWithPseudoFacts(f, liftedAction.getEffects(), true)) {
                    liftedActionsAvailableForThisLayerElmWithGroundPredAsPosEff.add(liftedAction);
                }
            }

            if (liftedActionsAvailableForThisLayerElmWithGroundPredAsPosEff.size() > 0) {

                for (LiftedAction liftedAction : liftedActionsAvailableForThisLayerElmWithGroundPredAsPosEff) {
                    rule15.append("(assert (=> (and (not " + fluentCurrentLayerElm + ") " + fluentNextLayerElm + " "
                            + liftedAction.getUniqueName() + ") (or ");
                    for (PseudoFact effect : liftedAction.getEffects()) {
                        if (!effect.isPositive() || !effect.getPredicateName().equals(namePredicate)) {
                            continue;
                        }

                        // boolean allParamsAreConstants = true;
                        // for (int argi = 0; argi < effect.getScopeVariables().size(); argi++) {
                        // if (!effect.getScopeVariables().get(argi).isConstant()) {
                        // allParamsAreConstants = false;
                        // break;
                        // }
                        // }
                        // if (allParamsAreConstants) {
                        // continue;
                        // }
                        rule15.append("(and true ");
                        for (int argi = 0; argi < effect.getScopeVariables().size(); argi++) {
                            if (effect.getScopeVariables().get(argi).isConstant()) {
                                continue;
                            }
                            String paramLiftedAction = effect.getScopeVariables().get(argi).getUniqueName();
                            String groundName = parametersGroundFact.get(argi);
                            rule15.append(paramLiftedAction + "_" + groundName + " ");
                        }
                    }
                    rule15.append("))))\n");
                }
            }
        }
        return rule15.toString();
    }

    public String addConstrainsLayer(int layer) {

        StringBuilder constrainsInitState = new StringBuilder();

        if (layer == 0) {
            System.out.println("Constrains rule 1");
            constrainsInitState.append("; rule 1: Reduction initial task network\n");
            String rule1 = rule1_reduc_init_task_network();
            constrainsInitState.append(rule1);

            System.out.println("Constrains rule 2");
            constrainsInitState.append("; rule 2: Initals facts hold at pos 0\n");
            String rule2 = rule2_declaration_init_facts();
            constrainsInitState.append(rule2);
        }

        // First add all transition constraints
        if (layer > 0) {
            int numberLayerElementPreviousLayer = this.layers.get(layer - 1).layerElements.size();

            System.out.println("Constrains rule 7 and 8");
            for (int layerElementIdx = 0; layerElementIdx < numberLayerElementPreviousLayer; layerElementIdx++) {
                constrainsInitState.append("; ==== layer: " + (layer - 1) + " layerElement: " + layerElementIdx + "/"
                        + (numberLayerElementPreviousLayer - 1) + " =====\n");
                constrainsInitState.append("; rule 7: Ground fact must be equal to successor at next layer\n");
                String rule7 = rule_7_transitionnal_ground_fact(layer - 1, layerElementIdx);
                constrainsInitState.append(rule7);

                constrainsInitState.append("; rule 8: Transitionnal methods\n");
                String rule8 = rule_8_transitionnal_operators(layer - 1, layerElementIdx);
                constrainsInitState.append(rule8);
            }

        }

        int numberLayerElm = this.layers.get(layer).layerElements.size() - 1;

        for (int layerElementIdx = 0; layerElementIdx < numberLayerElm; layerElementIdx++) {
            System.out
                    .println("For layer: " + layer + " layerElement: " + layerElementIdx + "/" + (numberLayerElm - 1));
            constrainsInitState.append("; ==== layer: " + layer + " layerElement: " + layerElementIdx + "/"
                    + (numberLayerElm - 1) + " =====\n");

            System.out.println("Constrains rule 3");
            constrainsInitState.append("; rule 3: Action is primitive and reduction in not primitive\n");
            String rule3 = rule3_action_is_prim_reduct_in_not_prim(layer, layerElementIdx);
            constrainsInitState.append(rule3);

            System.out.println("Constrains rule 4");
            constrainsInitState.append("; rule 4: At most one action and reduction\n");
            String rule4 = rule4_at_most_one_action_and_reduction(layer, layerElementIdx);
            constrainsInitState.append(rule4);

            System.out.println("Constrains rule 5");
            constrainsInitState.append("; rule 5: Operation implies preconditions\n");
            String rule5 = rule5_operation_implies_preconditions(layer, layerElementIdx);
            constrainsInitState.append(rule5);

            System.out.println("Constrains rule 6");
            constrainsInitState.append("; rule 6: Actions implies effects\n");
            String rule6 = rule6_action_implies_effects(layer, layerElementIdx);
            constrainsInitState.append(rule6);

            System.out.println("Constrains rule 12");
            constrainsInitState.append("; rule 12: Operator true implies scope var at least one value\n");
            String rule12 = rule12_operator_true_implies_scope_var_at_least_one_value(layer, layerElementIdx);
            constrainsInitState.append(rule12);

            System.out.println("Constrains rule 13");
            constrainsInitState.append("; rule 13: Substituing pseudo fact to ground fact\n");
            String rule13 = rule13_substituing_pseudo_fact_to_ground_fact(layer, layerElementIdx);
            constrainsInitState.append(rule13);

            System.out.println("Constrains rule 14");
            constrainsInitState.append("; rule 14: Frame axioms\n");
            String rule14 = rule14_frame_axioms(layer, layerElementIdx);
            constrainsInitState.append(rule14);

            System.out.println("Constrains rule 15");
            constrainsInitState.append("; rule 15: Predicate change implies specific grounding\n");
            String rule15 = rule15_predicate_change_implies_specific_grounding(layer, layerElementIdx);
            constrainsInitState.append(rule15);
        }

        System.out.println("Constrains rule 11");
        constrainsInitState.append("; rule 11: Scope var can take at most one value\n");
        String rule11 = rule11_scope_var_can_take_at_most_one_value();
        constrainsInitState.append(rule11);

        System.out.println("Constrains rule 10");
        constrainsInitState.append("; rule 10: Layer is fully primitive\n");
        String rule10 = rule10_layer_is_fully_primitive(layer);
        constrainsInitState.append(rule10);

        return constrainsInitState.toString();
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
     * Create the first layer and the layer elements in it
     */
    public void initializeFirstLayerAndLayerElms() {
        Layer firstLayer = new Layer();

        // Iterate through the tasks in the initial task network
        for (int i = 0; i < this.problem.getInitialTaskNetwork().getTasks().size(); i++) {
            LayerElement layerElm = new LayerElement(-1);
            firstLayer.layerElements.add(layerElm);
        }

        // Add as well a layer element for the goal
        LayerElement finalLayerElm = new LayerElement(-1);
        firstLayer.layerElements.add(finalLayerElm);

        // Add the first layer to the list of layers
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
        ;

        // Create the child position of each position
        for (int parentPositionIdx = 0; parentPositionIdx < this.layers.lastElement().layerElements
                .size(); parentPositionIdx++) {
            // Create the correct number of child for this layer
            for (int childPosition = 0; childPosition < this.layers.lastElement().e
                    .get(parentPositionIdx); childPosition++) {
                LayerElement layerElm = new LayerElement(parentPositionIdx);
                nextLayer.layerElements.add(layerElm);
            }
        }

        this.layers.add(nextLayer);
    }

    /**
     * Get the position of the parenet layerElement which has created the layer
     * specified by the layerIdx and layerPosition
     * 
     * @param layerIdx      LayerIdx of the child LayerElement
     * @param layerPosition LayerPosition of the child LayerElement
     * @return LayerPosition of the parent LayerElement
     */
    public int getParentPosition(int layerIdx, int layerPosition) {
        return this.layers.get(layerIdx).layerElements.get(layerPosition).getParentPosition();
    }

    /**
     * Get a unique ID for the couple (layer, position)
     * 
     * @param layer
     * @param position
     * @return Unqiue ID for the couple (layer, position)
     */
    public int GetUniqueIDForLayerAndPosition(int layer, int position) {
        // The unique ID will simple be
        // sum(layer_i * size layer_i) for i in range(0, layer) + position

        int uniqueID = 0;
        for (int layerIdx = 0; layerIdx < layer; layerIdx++) {
            uniqueID += this.layers.get(layerIdx).layerElements.size();
        }

        uniqueID += position;

        return uniqueID;
    }

    public void computeNextandMaxAmountOfChildOfEachLayerElm(int idxLayer) {

        int firstChildPosition = 0;
        int maximumChildren = 0;
        Layer layer = this.layers.get(idxLayer);

        for (LayerElement layerElm : layer.layerElements) {

            layer.n.add(firstChildPosition);
            maximumChildren = layerElm.computeNumberChildren(this.liftedMethodToNumberSubtasks);
            layer.e.add(maximumChildren);

            firstChildPosition += maximumChildren;
        }
    }

    public String encodeFirstLayer() {
        initializeFirstLayerAndLayerElms();

        System.out.println("Compute initial state clauses");
        // String initialStateConstrains = addInitialStateConstrains();
        String initialStateConstrains = addConstrainsLayer(0);

        this.allClauses.append(initialStateConstrains);

        int layerIdx = 0;

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

        allLiftedActionsLastLayer.clear();

        // Compute the n(l, i) and e(l, i) of the previous layer
        computeNextandMaxAmountOfChildOfEachLayerElm(layerIdx - 1);

        // Initialize new layer
        initializeNextLayerAndLayerElms();

        System.out.println("======= Add constrains layer " + layerIdx + " =======");

        // Add transitionnal clauses from previous layer to current layer
        String constrainsLayer = addConstrainsLayer(layerIdx);

        this.allClauses.append(constrainsLayer);

        System.out.println("Layer is completly encoded !");

        return this.allClauses.toString();
    }
}
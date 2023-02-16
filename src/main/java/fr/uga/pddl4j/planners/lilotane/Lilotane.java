package fr.uga.pddl4j.planners.lilotane;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;
import java.util.stream.Stream;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import java.util.Comparator;
import java.util.HashMap;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.io.InputStreamReader;

import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.parser.ParsedDomain;
import fr.uga.pddl4j.parser.Parser;
import fr.uga.pddl4j.parser.SAS_Plus.SASplusLiftedFamGroup;
import fr.uga.pddl4j.plan.Hierarchy;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.planners.htn.AbstractHTNPlanner;
import fr.uga.pddl4j.planners.htn.stn.AbstractSTNPlanner;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Pair;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import picocli.CommandLine;

import fr.uga.pddl4j.planners.lilotane.LilotaneOptimization;;

@CommandLine.Command(name = "Lilotane", version = "Lilotane 0.1", description = "Solves a specified classical problem using SMT encoding.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")
public class Lilotane extends AbstractHTNPlanner {

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(Lilotane.class.getName());

    private String path_exec_VAL = "src/test/resources/validators/pandaPIparser";

    private String filenameSMT = "test.SMT";

    private LilotaneOptimization optimizationsTouse = new LilotaneOptimization(false, false, false);

    /**
     * Instantiates the planning problem from a parsed problem.
     *
     * @param problem the problem to instantiate.
     * @return the instantiated planning problem or null if the problem cannot be
     *         instantiated.
     */
    @Override
    public Problem instantiate(DefaultParsedProblem problem) {
        final Problem pb = new DefaultProblem(problem);
        pb.instantiate();
        // long beginComputeSASplus = System.currentTimeMillis();
        // System.out.println("Start to determinate lifted fam mutex..");
        // SASplusLiftedFamGroup.determinateLiftedFamGroups(pb);
        // long deltabeginComputeSASplus = System.currentTimeMillis() -
        // beginComputeSASplus;
        // System.out.println("Time to compute mutex: " + deltabeginComputeSASplus + "
        // ms");
        return pb;
    }

    /**
     * Command line option to set the full path of the file to store the plan found.
     * 
     * @param outputFullPathFile Full path of the file to store the plan found
     */
    @CommandLine.Option(names = { "-s",
            "--use-sas-plus" }, description = "Use SAS+")
    public void useSASPlus(boolean _) {
        this.optimizationsTouse.useSASplus = true;
    }

    /**
     * Command line option to set the full path of the file to store the plan found.
     * 
     * @param outputFullPathFile Full path of the file to store the plan found
     */
    @CommandLine.Option(names = { "-o",
            "--use-one-var-per-action-layer-element" }, description = "Use one integer variable to encode all possible actions for each layer element")
    public void useOneVarToEncodeAllActionsAtLayerAndPos(boolean _) {
        this.optimizationsTouse.useOneVarToEncodeAllActionsAtLayerAndPos = true;
    }

    /**
     * Writes the given clauses and variables to the SMT file.
     *
     * @param allBoolVariables the boolean variables to write to the file
     * @param allIntVariables  the integer variables to write to the file
     * @param clauses          the clauses to write to the file
     * @throws IOException if there is an error in writing to the file
     */
    void writeIntoSMTFile(Vector<String> allBoolVariables, Vector<String> allIntVariables,
            String declarationObjectsAndPredicates, String clauses, LilotaneEncoder encoder)
            throws IOException {
        BufferedWriter writer;

        writer = new BufferedWriter(new FileWriter(this.filenameSMT));

        writer.write("(set-logic QF_ALL)\n");
        writer.write("(set-option :produce-models true)\n");

        // writer.write(declarationObjectsAndPredicates);

        // Declare all of our methods and indicate the scope of the variables
        // int numLayers = encoder.layers.size();
        // for (int layerIdx = 0; layerIdx < encoder.layers.size(); layerIdx++) {
        // Layer layer = encoder.layers.get(layerIdx);
        // for (int layerElmIdx = 0; layerElmIdx < layer.layerElements.size();
        // layerElmIdx++) {
        // LayerElement layerElm =layer.layerElements.get(layerElmIdx);
        // for (String methodName : layerElm.getLiftedReductionWithScope().keySet()) {
        // String methodWithLayerAndElm = encoder.addLayerAndPos(methodName, layerIdx,
        // layerElmIdx);
        // writer.write("(declare-const METHOD_" + methodWithLayerAndElm + " Bool)\n");
        // ArrayList<HashSet<String>> scopeVariables =
        // layerElm.getLiftedReductionWithScope().get(methodName);
        // for (int argi = 0; argi < scopeVariables.size(); argi++) {
        // writer.write("(declare-const METHOD_" + methodWithLayerAndElm + "%ARG" + argi
        // + " Int)\n");
        // writer.write("(assert (or ");
        // for (String obj : scopeVariables.get(argi)) {
        // writer.write("(= METHOD_" + methodWithLayerAndElm + "%ARG" + argi + " " + obj
        // + ") ");
        // }
        // writer.write("))\n");
        // }
        // }
        // for (String actionName : layerElm.getLiftedActionWithScope().keySet()) {
        // String methodWithLayerAndElm = encoder.addLayerAndPos(actionName, layerIdx,
        // layerElmIdx);
        // writer.write("(declare-const ACTION_" + methodWithLayerAndElm + " Bool)\n");
        // }
        // }
        // }

        // Declare all the variables
        for (String var : allBoolVariables) {
            writer.write("(declare-const " + var + " Bool)\n");
        }
        for (String var : allIntVariables) {
            writer.write("(declare-const " + var + " Int)\n");
        }

        // Declare the value that can be taken by each scope variables
        // for (ScopeVariable scopeVar : encoder.allScopeVariables) {
        // if (!scopeVar.isConstant()) {
        // for (String valueTaken : scopeVar.getPossibleValueVariable()) {
        // writer.write("(declare-const " + scopeVar.getUniqueName() + "_" + valueTaken
        // + " Bool)\n");
        // }
        // }
        // }

        // Write the clauses
        writer.write(clauses);

        writer.write("(check-sat)\n");
        writer.write("(get-model)\n");
        writer.write("(exit)\n");
        writer.flush();
        writer.close();
    }

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
     * Executes the SMT solver on the SMT file and returns the response as a string.
     *
     * @return the response of the SMT solver as a string
     */
    String executeSMTSolverOnFile() {
        String outputSMTSolver = "";
        String executableSolverSMT = "cvc5";
        String command = "./" + executableSolverSMT + " " + this.filenameSMT + " --lang smt";
        try {
            Process p = Runtime.getRuntime().exec(command);
            BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String newLine = "";

            while ((newLine = reader.readLine()) != null) {
                outputSMTSolver += newLine + "\n";
            }
            p.waitFor();
        } catch (IOException | InterruptedException e1) {
            e1.printStackTrace();
        }
        return outputSMTSolver;
    }

    /**
     * Returns true if the given response of the SMT solver indicates that the SMT
     * file is satisfiable, false otherwise.
     *
     * @param response the response of the SMT solver
     * @return true if the SMT file is satisfiable, false otherwise
     */
    private Boolean fileIsSatisfiable(String responseSolverSMT) {
        return !responseSolverSMT.contains("unsat");
    }

    SequentialPlan extractPlanAndHierarchyFromSolver(Problem problem, String outputSMTSolver, int lastLayer,
            LilotaneEncoder encoder) {

        String[] outputLines = outputSMTSolver.split("\n");

        List<String> actionsInPlan = Arrays.asList(outputLines);
        List<String> scopeVarActions = Arrays.asList(outputLines);

        // First, extract all the actions of the last layer which are true
        actionsInPlan = Arrays.asList(actionsInPlan.stream()
                .filter(s -> (s.contains("ACTION-") && s.contains("__" + lastLayer) && s.contains(" true)")))
                .toArray(String[]::new));
        scopeVarActions = Arrays
                .asList(scopeVarActions.stream().filter(s -> s.contains(" SCOPE_") && s.contains(" true)")).toArray(String[]::new));

        // We also need to sort by layer and then by position
        actionsInPlan = Arrays.asList(actionsInPlan.stream().sorted(Comparator
                .comparingInt((String s) -> Integer.parseInt(s.split(" ")[1].split("__")[1].split("_")[0])) // Sort
                                                                                                            // by
                                                                                                            // layer
                .thenComparingInt((String s) -> Integer.parseInt(s.split(" ")[1].split("__")[1].split("_")[1])) // Sort
                                                                                                                // by
                                                                                                                // position
                                                                                                                // in
                                                                                                                // layer
        ).toArray(String[]::new));

        Map<String, String> dictScopeToValue = new HashMap<String, String>();
        for (String lineScopeVarAndValue : scopeVarActions) {
            String scopeAndValue = lineScopeVarAndValue.split(" ")[1];
            String scopeVarIdx = scopeAndValue.split("_")[1];
            String value = scopeAndValue.substring("SCOPE_".length() + scopeVarIdx.length() + 1);
            dictScopeToValue.put("SCOPE_" + scopeVarIdx, value);
        }

        // Get the objects associated with each action
        List<LiftedAction> actionsObjInPlan = new ArrayList<LiftedAction>();

        for (String actionInPlan : actionsInPlan) {
            if (actionInPlan.contains("ACTION-Blank")) {
                actionsObjInPlan.add(null);
            } else {
                for (LiftedAction actionObj : encoder.allLiftedActionsLastLayer) {
                    if (actionInPlan.contains(actionObj.getUniqueName())) {
                        actionsObjInPlan.add(actionObj);
                    }
                }
            }
        }

        SequentialPlan p = new SequentialPlan();
        Hierarchy hierarchy = new Hierarchy();

        // Add the roots tasks to the hierarchy
        int numberRootTasks = problem.getInitialTaskNetwork().getTasks().size();
        for (int rootTaskIdx = 0; rootTaskIdx < numberRootTasks; rootTaskIdx++) {
            hierarchy.getRootTasks().add(rootTaskIdx);
            hierarchy.getDecomposition().put(rootTaskIdx, new ArrayList<>());
        }

        System.out.println("==============");
        for (int i = 0; i < actionsObjInPlan.size(); i++) {
            if (actionsObjInPlan.get(i) == null) {
                System.out.println("Element " + i + " : " + "BLANK");
                continue;
            }
            System.out.println("Element " + i + " : " + actionsObjInPlan.get(i).getUniqueName());
        }
        System.out.println("==============");
        // // take the first action executed
        for (LiftedAction actionObjInPlan : actionsObjInPlan) {

            if (actionObjInPlan == null) {
                continue;
            }

            int sizeRootFromAction = 0;
            // Get the parent of the action
            LiftedMethod parentMethod = actionObjInPlan.getParentMethod();
            while (parentMethod != null) {
                sizeRootFromAction++;
                parentMethod = parentMethod.getParentMethod();
            }

            int parentMethodId = -1;

            for (int i = sizeRootFromAction; i >= 0; i--) {


                ArrayList<String> argsMethod = new ArrayList<>();

                ArrayList<ScopeVariable> scopesVariableOperator = new ArrayList<>();

                // If this is an action
                if (i == 0) {

                    LiftedAction action = actionObjInPlan;

                    if (action.isNoopAction) {
                        continue;
                    }

                    scopesVariableOperator = action.getParameters();

                    // // Find all value of the scope of this method/action
                    for (ScopeVariable scopeVariable : scopesVariableOperator) {

                        if (scopeVariable.getPossibleValueVariable().size() == 1) {
                            argsMethod.add(scopeVariable.getPossibleValueVariable().iterator().next());
                            continue;
                        }
                        String nameScopeVariable = scopeVariable.getUniqueName();
                        
                        // Get the value from the dictionnary
                        argsMethod.add(dictScopeToValue.get(nameScopeVariable));
                    }

                    // Find the ground method associated with this method and argument
                    String nameAction = action.getName();

                    boolean actionIsFound = false;

                    for (Action groundAction : problem.getActions()) {

                        if (!groundAction.getName().equals(nameAction)) {
                            continue;
                        }

                        // System.out.println(argMethod);
                        // System.out.println(prettyDisplayAction(groundAction, problem));

                        boolean isCorrectAction = true;
                        for (int argi = 0; argi < groundAction.getInstantiations().length; argi++) {
                            if (!problem.getConstantSymbols().get(groundAction.getInstantiations()[argi])
                                    .equals(argsMethod.get(argi))) {
                                isCorrectAction = false;
                                break;
                            }
                        }

                        if (isCorrectAction) {

                            // Add it into our hierarchy if it not already there
                            // int methodId = this.problem.getMethods().indexOf(groundMethod);
                            int actionId = encoder.GetUniqueIDForLayerAndPosition(action.getLayer(), action.getLayerElement());
                            hierarchy.getPrimtiveTasks().put(actionId, groundAction);

                            // Add this method as the child of the parent method
                            if (parentMethodId != -1) {
                                hierarchy.getDecomposition().get(parentMethodId).add(actionId);
                            }
                            actionIsFound = true;
                            break;
                        }
                    }
                    if (!actionIsFound) {
                        System.out.println("Action not found");
                    }
                }
                // If this is a method
                else {

                    // Get the parent method
                    LiftedMethod method = actionObjInPlan.getParentMethod();
                    for (int j = 0; j < i - 1; j++) {
                        method = method.getParentMethod();
                    }

                    scopesVariableOperator = method.getParameters();

                    // Find all value of the scope of this method/action
                    for (ScopeVariable scopeVariable : scopesVariableOperator) {

                        if (scopeVariable.getPossibleValueVariable().size() == 1) {
                            argsMethod.add(scopeVariable.getPossibleValueVariable().iterator().next());
                            continue;
                        }
                        String nameScopeVariable = scopeVariable.getUniqueName();
                        
                        // Get the value from the dictionnary
                        argsMethod.add(dictScopeToValue.get(nameScopeVariable));
                    }

                    // Find the ground method associated with this method and argument
                    String nameMethod = method.getName();

                    for (Method groundMethod : problem.getMethods()) {

                        if (!groundMethod.getName().equals(nameMethod)) {
                            continue;
                        }

                        // System.out.println(argMethod);
                        // System.out.println(prettyDisplayMethod(groundMethod, problem));

                        boolean isCorrectMethod = true;
                        for (int argi = 0; argi < groundMethod.getInstantiations().length; argi++) {
                            if (!problem.getConstantSymbols().get(groundMethod.getInstantiations()[argi])
                                    .equals(argsMethod.get(argi))) {
                                isCorrectMethod = false;
                                break;
                            }
                        }

                        if (isCorrectMethod) {

                            // Add it into our hierarchy if it not already there
                            // int methodId = this.problem.getMethods().indexOf(groundMethod);
                            int methodId = encoder.GetUniqueIDForLayerAndPosition(method.getLayer(), method.getLayerElement());
                            if (!hierarchy.getCounpoudTasks().keySet().contains(methodId)) {
                                hierarchy.getCounpoudTasks().put(methodId, groundMethod);
                                hierarchy.getDecomposition().put(methodId, new ArrayList<>());
                            }

                            // Add this method as the child of the parent method
                            if (parentMethodId != -1
                                    && !hierarchy.getDecomposition().get(parentMethodId).contains(methodId)) {
                                hierarchy.getDecomposition().get(parentMethodId).add(methodId);
                            }

                            parentMethodId = methodId;
                            break;
                        }
                    }
                }
            }
        }

        // Create the sequential plan
        int timeStep = 0;
        for (Action action : hierarchy.getPrimtiveTasks().values()) {
            p.add(timeStep, action);
            timeStep++;
        }

        System.out.println(problem.toString(hierarchy));
        p.setHierarchy(hierarchy);

        return p;
    }

    /**
     * 
     * Display debugging information about the current layer, number of clauses,
     * number of boolean and numerical variables, and the solving and encoding
     * times.
     * 
     * @param layerIdx          the index of the current layer
     * @param clauses           the clauses generated by the encoder
     * @param allBoolVariables  the boolean variables generated by the encoder
     * @param allIntVariables   the numerical variables generated by the encoder
     * @param deltaEncodingTime the encoding time for the current layer
     * @param deltaSolvingTime  the solving time for the current layer
     */
    private void displayDebuggingInfo(int layerIdx, String clauses, Vector<String> allBoolVariables,
            Vector<String> allIntVariables, long deltaEncodingTime, long deltaSolvingTime) {

        // Display the debugging information using the LOGGER.info function
        LOGGER.info("Current layer: {}\n", layerIdx);
        LOGGER.info("Number of clauses: {}\n", clauses.split("\n").length);
        LOGGER.info("Number of boolean variables: {}\n", allBoolVariables.size());
        LOGGER.info("Number of numerical variables: {}\n", allIntVariables.size());
        LOGGER.info("Encoding time: {} ms\n", deltaEncodingTime);
        LOGGER.info("Solving time: {} ms\n", deltaSolvingTime);
    }

    @Override
    public Plan solve(Problem problem) {

        // Indicate which optimizations will be used when using the Lilotane encoder
        // this.optimizationsTouse.useSASplus = false;
        // this.optimizationsTouse.useOneVarToEncodeAllActionsAtLayerAndPos = false;
        // this.optimizationsTouse.useOneVarToEncodeAllMethodsAtLayerAndPos = false;

        // Show which optimizations are currently used
        this.optimizationsTouse.displayCurrentUsedOptimizations();

        // Initialize the variables which will store the encoding time and solving time
        long deltaInitializingLilotaneTime = 0;
        long deltaEncodingTime = 0;
        long deltaSolvingTime = 0;

        long beginInitializeLilotaneTime = System.currentTimeMillis();

        // Initialize the encoder
        LilotaneEncoder encoder = new LilotaneEncoder(problem, this.optimizationsTouse);

        // Record the encoding time for the initial layer
        deltaInitializingLilotaneTime = System.currentTimeMillis() - beginInitializeLilotaneTime;

        LOGGER.info("Initializing lilotane time: " + deltaInitializingLilotaneTime + " ms.\n");

        // Initialize the layer index and maximum number of layers
        int layerIdx = 0;
        int maxLayers = 4;

        // Initialize the encoding time for the initial layer
        long beginEncodeTime = System.currentTimeMillis();

        // Initialize the clauses and variables for the initial layer
        String clauses = encoder.encodeFirstLayer();
        String declarationObjectsAndpredicates = encoder.declarationObjectsAndPredicates.toString();
        Vector<String> allBoolVariables = encoder.getAllBoolVariables();
        Vector<String> allIntVariables = encoder.getAllIntVariables();

        int totalNumberVariables = allIntVariables.size() + allBoolVariables.size();
        LOGGER.info("Launch solver (number variables: " + totalNumberVariables + " number clauses: "
                + clauses.split("\n").length + "\n");

        // Write the clauses and variables to a file
        try {
            writeIntoSMTFile(allBoolVariables, allIntVariables, declarationObjectsAndpredicates, clauses, encoder);
        } catch (IOException e) {
            // Handle the exception
            e.printStackTrace();
        }

        // Record the encoding time for the initial layer
        deltaEncodingTime = System.currentTimeMillis() - beginEncodeTime;
        this.getStatistics().setTimeToEncode(this.getStatistics().getTimeToEncode() + deltaEncodingTime);

        // Initialize the solving time for the initial layer
        long beginSolveTime = System.currentTimeMillis();

        // Run the SMT solver on the file
        String responseSMT = executeSMTSolverOnFile();

        // Record the solving time for the initial layer
        deltaSolvingTime = System.currentTimeMillis() - beginSolveTime;
        this.getStatistics().setTimeToSearch(this.getStatistics().getTimeToSearch() + deltaSolvingTime);

        displayDebuggingInfo(layerIdx, clauses, allBoolVariables, allIntVariables, deltaEncodingTime, deltaSolvingTime);

        boolean fileIsSatisfiable = fileIsSatisfiable(responseSMT);

        // Solve the SMT file until it is satisfiable or the maximum number of layers is
        // reached
        while (!fileIsSatisfiable && layerIdx < maxLayers) {
            // Increment the layer index
            layerIdx++;

            // Initialize the encoding time for the next layer
            beginEncodeTime = System.currentTimeMillis();

            // Get the new clauses and variables
            clauses = encoder.encodeNextLayer(layerIdx);
            allBoolVariables = encoder.getAllBoolVariables();
            allIntVariables = encoder.getAllIntVariables();

            // Write the clauses and variables to a file
            try {
                LOGGER.info("Write into SMT file...\n");
                writeIntoSMTFile(allBoolVariables, allIntVariables, encoder.declarationObjectsAndPredicates.toString(),
                        clauses, encoder);
            } catch (IOException e) {
                // Handle the exception
                e.printStackTrace();
            }

            // Record the encoding time
            deltaEncodingTime = System.currentTimeMillis() - beginEncodeTime;
            this.getStatistics().setTimeToEncode(this.getStatistics().getTimeToEncode() + deltaEncodingTime);

            // Initialize the solving time for the next layer
            beginSolveTime = System.currentTimeMillis();

            // Run the SMT solver on the file
            LOGGER.info("Launch solver on SMT file...\n");
            responseSMT = executeSMTSolverOnFile();

            fileIsSatisfiable = fileIsSatisfiable(responseSMT);

            // Record the solving time
            deltaSolvingTime = System.currentTimeMillis() - beginSolveTime;
            this.getStatistics().setTimeToSearch(this.getStatistics().getTimeToSearch() + deltaSolvingTime);

            displayDebuggingInfo(layerIdx, clauses, allBoolVariables, allIntVariables, deltaEncodingTime,
                    deltaSolvingTime);
        }

        // If the SMT file is satisfiable, extract the plan from the response
        if (fileIsSatisfiable) {

            // Write the output of the SMT solver to a file for debugging purpose
            File resultSMTFile;
            try {
                resultSMTFile = File.createTempFile("tmp_result_SMT", ".txt");

                BufferedWriter writer = new BufferedWriter(new FileWriter(resultSMTFile));
                writer.write(responseSMT);
                writer.close();
            } catch (IOException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }

            LOGGER.info("Extract the hierarchy of the plan...\n");
            // SequentialPlan plan = extractPlanAndHierarchyFromSolver(problem, responseSMT,
            // encoder, layerIdx, this.optimizationsTouse);
            SequentialPlan plan = extractPlanAndHierarchyFromSolver(problem, responseSMT, layerIdx, encoder);

            // Verify if the plan is valid
            LOGGER.info("Check if plan is valid...\n");
            boolean planIsValid;
            try {
                planIsValid = validatePlan(problem, plan);
            } catch (IOException e) {
                LOGGER.error("Failed to check if plan is valid !\n");
                planIsValid = false;
            }

            if (planIsValid) {
                LOGGER.info("Plan is valid !\n");

                LOGGER.info("Preprocessing time (ms): " + deltaInitializingLilotaneTime + "\n");
                LOGGER.info("Encoding time (ms): " + this.getStatistics().getTimeToEncode() + "\n");
                LOGGER.info("Solving time (ms): " + this.getStatistics().getTimeToSearch() + "\n");
                return plan;
            } else {
                LOGGER.error("Plan is not valid !\n");
            }

        }
        // If the SMT file is not satisfiable, return null
        return null;
    }

    /**
     * Validates a given plan by writing the plan's hierarchy to a file and
     * executing a command to verify the plan.
     * If the plan is valid, the function returns true. If the plan is invalid or if
     * there is an error in executing
     * the command, the function returns false.
     *
     * @param problem the problem for which the plan is being validated
     * @param plan    the plan to validate
     * @return true if the plan is valid, false otherwise
     * @throws IOException if there is an error in writing to the file or executing
     *                     the command
     */
    public boolean validatePlan(Problem problem, Plan plan) throws IOException {
        // Create a temporary file to store the hierarchy of the plan
        File planFile = File.createTempFile("tmp_plan", ".txt");

        // Write the hierarchy of the plan to the file
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(planFile))) {
            writer.write(problem.toString(plan.getHierarchy()));
        }

        // Construct the command to verify the plan
        String command = String.format("./%s --verify %s %s %s", this.path_exec_VAL, this.getDomain(),
                this.getProblem(), planFile.getAbsolutePath());

        System.out.println(command);

        // Execute the command and store the output
        String output = executeCommand(command);

        // Split the output into separate lines
        String[] lines = output.split("\n");

        // Get the last line of the output
        String lastLine = lines[lines.length - 1];

        // Check if the last line contains the string "Plan verification result"
        if (!lastLine.contains("Plan verification result")) {
            // If the last line does not contain the string "Plan verification result", log
            // an error and return false
            LOGGER.error("Cannot verify the plan given. Output returned by executable: \n" + output);
            return false;
        }
        // If the last line contains the string "Plan verification result", return true
        // if the last line also contains the string "true"
        return lastLine.contains("true");
    }

    /**
     * Executes a command and returns the output as a string.
     *
     * @param command the command to execute
     * @return the output of the command as a string
     * @throws IOException if there is an error in executing the command
     */
    private String executeCommand(String command) throws IOException {
        StringBuilder output = new StringBuilder();
        Process p = Runtime.getRuntime().exec(command);
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
            String line;
            while ((line = reader.readLine()) != null) {
                output.append(line).append("\n");
            }
        }
        return output.toString();
    }

    /**
     * The main method of the <code>SMT</code> planner.
     *
     * @param args the arguments of the command line.
     */
    public static void main(String[] args) {

        try {
            final Lilotane planner = new Lilotane();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }
}
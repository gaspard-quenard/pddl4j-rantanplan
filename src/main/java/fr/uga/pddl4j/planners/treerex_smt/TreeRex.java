package fr.uga.pddl4j.planners.treerex_smt;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;
import java.util.stream.Stream;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import java.util.Comparator;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.io.InputStreamReader;

import fr.uga.pddl4j.parser.DefaultParsedProblem;
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

@CommandLine.Command(name = "TreeRex", version = "TreeRex 0.1", description = "Solves a specified classical problem using SMT encoding.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")
public class TreeRex extends AbstractHTNPlanner {

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(TreeRex.class.getName());

    private String path_exec_VAL = "src/test/resources/validators/pandaPIparser";

    private String filenameSMT = "test.SMT";

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
        return pb;
    }

    /**
     * Writes the given clauses and variables to the SMT file.
     *
     * @param allBoolVariables the boolean variables to write to the file
     * @param allIntVariables  the integer variables to write to the file
     * @param clauses          the clauses to write to the file
     * @throws IOException if there is an error in writing to the file
     */
    void writeIntoSMTFile(Vector<String> allBoolVariables, Vector<String> allIntVariables, String clauses)
            throws IOException {
        BufferedWriter writer;

        writer = new BufferedWriter(new FileWriter(this.filenameSMT));

        writer.write("(set-logic QF_LIA)\n");
        writer.write("(set-option :produce-models true)\n");

        // Declare all the variables
        for (String var : allBoolVariables) {
            writer.write("(declare-const " + var + " Bool)\n");
        }
        for (String var : allIntVariables) {
            writer.write("(declare-const " + var + " Int)\n");
        }

        // Write the clauses
        writer.write(clauses);

        writer.write("(check-sat)\n");
        writer.write("(get-model)\n");
        writer.write("(exit)\n");
        writer.flush();
        writer.close();
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

    /**
     * Extracts a plan and hierarchy from the output of the SMT solver.
     * 
     * @param problem         the problem to solve
     * @param outputSMTSolver the output of the SMT solver
     * @param encoder         the encoder used to encode the problem
     * @param layerIdx        the current layer index
     * @return the extracted plan and hierarchy
     */
    private SequentialPlan extractPlanAndHierarchyFromSolver(Problem problem, String outputSMTSolver,
            TreeRexEncoder encoder, int layerIdx, TreeRexOptimization optimizationsToUse) {

        SequentialPlan p = new SequentialPlan();
        Hierarchy hierarchy = new Hierarchy();

        // Add the roots tasks to the hierarchy
        int numberRootTasks = problem.getInitialTaskNetwork().getTasks().size();
        for (int rootTaskIdx = 0; rootTaskIdx < numberRootTasks; rootTaskIdx++) {
            hierarchy.getRootTasks().add(rootTaskIdx);
            hierarchy.getDecomposition().put(rootTaskIdx, new ArrayList<>());
        }

        String[] values = outputSMTSolver.split("\n");

        List<String> lValues = Arrays.asList(values);

        // Only keep the actions and methods which are true (do not keep blank action as
        // well)

        if (!optimizationsToUse.useOneVarToEncodeAllActionsAtLayerAndPos) {
            lValues = Arrays.asList(lValues.stream().filter(s -> ((s.contains(" ACTION_") || s.contains(" METHOD_"))
            && s.contains(" true)") && !s.contains("_Blank_"))).toArray(String[]::new));
        } else {
            lValues = Arrays.asList(lValues.stream().filter(s -> ((s.contains("CLIQUE_ACTION__") || (s.contains(" METHOD_"))
            && s.contains(" true)")))).toArray(String[]::new)); 
        }


        // We also need to sort by layer and then by position
        lValues = Arrays.asList(lValues.stream().sorted(Comparator
                .comparingInt((String s) -> Integer.parseInt(s.split(" ")[1].split("__")[1].split("_")[0])) // Sort by
                                                                                                            // layer
                .thenComparingInt((String s) -> Integer.parseInt(s.split(" ")[1].split("__")[1].split("_")[1])) // Sort
                                                                                                                // by
                                                                                                                // position
                                                                                                                // in
                                                                                                                // layer
        ).toArray(String[]::new));

        // Now, we will iterate our layers to see which reductions and which actions are
        // true
        // Let's start with the layer 0 element 0 for example and see which reduction
        // can occur

        for (int i = 0; i < encoder.layers.get(0).layerElements.size(); i++) {
            Vector<Method> reductionPossibleAtThisLayerAndElement = encoder.layers.get(0).layerElements.get(i)
                    .getReductions();

            // Find which reduction is true
            for (Method m : reductionPossibleAtThisLayerAndElement) {
                // What would be the name of the method m in the SMT file ?
                String methodName = encoder.addLayerAndPos(encoder.prettyDisplayMethod(m, problem), 0, i);
                String fullLineMethodTrueInSMTFile = "(define-fun " + methodName + " () Bool true)";
                // Check if method is true
                boolean methodIsTrue = lValues.contains(fullLineMethodTrueInSMTFile);
                if (methodIsTrue) {
                    // Get the decomposition of this method
                    recursiveGetHierarchyMethod(problem, lValues, encoder, hierarchy, m, 0, i, optimizationsToUse);
                    break; // Only one method can be true
                }
            }
        }

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
     * Recursively constructs a hierarchy for the given method by analyzing its
     * subtasks.
     *
     * @param problem              the problem being solved
     * @param linesOutputSMTSolver the output from the SMT solver, used to determine
     *                             which methods and actions are true
     * @param encoder              a TreeRexEncoder object used to encode the
     *                             problem with the TreeRex encoding
     * @param hierarchy            the hierarchy object being constructed
     * @param method               the method to analyze
     * @param layer                the layer of the method in the hierarchy
     * @param position             the position of the method within its layer
     */
    void recursiveGetHierarchyMethod(Problem problem, List<String> linesOutputSMTSolver,
            TreeRexEncoder encoder, Hierarchy hierarchy, Method method, Integer layer, Integer position, TreeRexOptimization optimizationsToUse) {

        // Get an unique ID for the method depending of its layer and position
        Integer methodID = encoder.GetUniqueIDForLayerAndPosition(layer, position);

        // Add the method into our hierarchy
        hierarchy.getCounpoudTasks().put(methodID, method);
        hierarchy.getDecomposition().put(methodID, new ArrayList<>());

        // Find the layer and element of the first child of this method
        Integer layerChildMethod = layer + 1;
        Integer positionChildMethod = encoder.layers.get(layer).n.get(position);

        // Iterate over all subtasks of this method
        for (Integer subtaskIdx : method.getSubTasks()) {

            // Get the subtask object
            Task subtask = problem.getTasks().get(subtaskIdx);

            // If the subtask is accomplish by an action
            if (subtask.isPrimtive()) {

                // Get the action which accomplish the method
                Action action = problem.getActions().get(problem.getTaskResolvers().get(subtaskIdx).get(0));

                // Verify that this action is true in the SMT file at the correct layer and
                // position
                final String lineActionTrueInSMTFile;

                if (!optimizationsToUse.useOneVarToEncodeAllActionsAtLayerAndPos) {
                    lineActionTrueInSMTFile = "(define-fun " + encoder.addLayerAndPos(encoder.prettyDisplayAction(action, problem),
                    layerChildMethod, positionChildMethod) + " () Bool true)";
                } else {
                    lineActionTrueInSMTFile = "(define-fun " + encoder.addLayerAndPos(encoder.getCliqueAction(),
                    layerChildMethod, positionChildMethod) + " () Int " + problem.getActions().indexOf(action) + ")";
                }

                if (!linesOutputSMTSolver.contains(lineActionTrueInSMTFile)) {
                    LOGGER.error("Impossible !");
                    return;
                }

                // Get the action unique ID
                Integer actionID = encoder.GetUniqueIDForLayerAndPosition(layerChildMethod, positionChildMethod);

                // Add this action into the hierarchy
                hierarchy.getPrimtiveTasks().put(actionID, action);
                hierarchy.getDecomposition().get(methodID).add(actionID);

            } else {
                // If the subtask is not primitive, find all methods which can resolve this
                // subtask and find which one of them is true in the SMT file, then add it to
                // the hierarchy as well
                // as the LinkedList

                // Get all the methods which can solve this task
                for (Method subMethod : problem.getMethods()) {

                    if (subMethod.getTask() == subtaskIdx) {

                        // Check if this method is true in the SMT file
                        String subMethodName = encoder.addLayerAndPos(encoder.prettyDisplayMethod(subMethod, problem),
                                layerChildMethod, positionChildMethod);

                        if (linesOutputSMTSolver.contains("(define-fun " + subMethodName + " () Bool true)")) {

                            // Get the unique ID of the submethod
                            Integer subMethodUniqueID = encoder.GetUniqueIDForLayerAndPosition(layerChildMethod,
                                    positionChildMethod);

                            // Add this methid as the decomposition of the parent method
                            hierarchy.getDecomposition().get(methodID).add(subMethodUniqueID);

                            // Recursive call this function to decompose it further
                            recursiveGetHierarchyMethod(problem, linesOutputSMTSolver, encoder, hierarchy, subMethod,
                                    layerChildMethod, positionChildMethod, optimizationsToUse);

                            break; // There can be only one method which is true as the decomposition
                        }
                    }
                }
            }
            // Update the position element for the next child
            positionChildMethod++;
        }
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

        // Use SAS+ encoding
        boolean useSASplus = true;

        // Indicate which optimizations will be used when using the TreeRex encoder
        TreeRexOptimization optimizationsToUse = new TreeRexOptimization(useSASplus, true, false);

        // Initialize the variables which will store the encoding time and solving time
        long deltaInitializingTreeRexTime = 0;
        long deltaEncodingTime = 0;
        long deltaSolvingTime = 0;

        long beginInitializeTreeRexTime = System.currentTimeMillis();

        // Initialize the encoder
        TreeRexEncoder encoder = new TreeRexEncoder(problem, optimizationsToUse);

        // Record the encoding time for the initial layer
        deltaInitializingTreeRexTime = System.currentTimeMillis() - beginInitializeTreeRexTime;

        LOGGER.info("Initializing tree rex time: " + deltaInitializingTreeRexTime + " ms.\n");

        // Initialize the layer index and maximum number of layers
        int layerIdx = 0;
        int maxLayers = 10;


        // Initialize the encoding time for the initial layer
        long beginEncodeTime = System.currentTimeMillis();

        // Initialize the clauses and variables for the initial layer
        String clauses = encoder.encodeFirstLayer();
        Vector<String> allBoolVariables = encoder.getAllBoolVariables();
        Vector<String> allIntVariables = encoder.getAllIntVariables();

        int totalNumberVariables = allIntVariables.size() + allBoolVariables.size();
        LOGGER.info("Launch solver (number variables: " + totalNumberVariables + " number clauses: "
                + clauses.split("\n").length + "\n");

        // Write the clauses and variables to a file
        try {
            writeIntoSMTFile(allBoolVariables, allIntVariables, clauses);
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

        // Solve the SMT file until it is satisfiable or the maximum number of layers is
        // reached
        while (!fileIsSatisfiable(responseSMT) && layerIdx < maxLayers) {
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
                writeIntoSMTFile(allBoolVariables, allIntVariables, clauses);
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

            // Record the solving time
            deltaSolvingTime = System.currentTimeMillis() - beginSolveTime;
            this.getStatistics().setTimeToSearch(this.getStatistics().getTimeToSearch() + deltaSolvingTime);

            displayDebuggingInfo(layerIdx, clauses, allBoolVariables, allIntVariables, deltaEncodingTime,
                    deltaSolvingTime);
        }

        // If the SMT file is satisfiable, extract the plan from the response
        if (fileIsSatisfiable(executeSMTSolverOnFile())) {

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
            SequentialPlan plan = extractPlanAndHierarchyFromSolver(problem, responseSMT, encoder, layerIdx, optimizationsToUse);

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
            final TreeRex planner = new TreeRex();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }
}
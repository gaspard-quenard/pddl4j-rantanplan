package fr.uga.pddl4j.planners.treerex_smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
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
     * @param problem the problem to solve
     * @param outputSMTSolver the output of the SMT solver
     * @param encoder the encoder used to encode the problem
     * @param layerIdx the current layer index
     * @return the extracted plan and hierarchy
     */
    private SequentialPlan extractPlanAndHierarchyFromSolver(Problem problem, String outputSMTSolver,
            TreeRexEncoder encoder, int layerIdx) {

        SequentialPlan p = new SequentialPlan();
        Hierarchy hierarchy = new Hierarchy();

        List<Integer> ActionsID = new ArrayList<>();
        List<Integer> MethodID = new ArrayList<>();
        List<Integer> PlaceToInsertActionInMethod = new ArrayList<>();

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
        lValues = Arrays.asList(lValues.stream().filter(s -> ((s.contains(" ACTION_") || s.contains(" METHOD_"))
                && s.contains(" true)") && !s.contains("_Blank_"))).toArray(String[]::new));

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

        for (int i = 0; i < lValues.size(); i++) {
            String s = lValues.get(i);

            String[] words = s.split(" ");
            if (words.length > 4) {

                // Pass while we are not on the last layer
                // words in the form: (define-fun METHOD_m1_go_ordering_0_f3_f0_f1_p1__3_9 ()
                // Bool false)
                int layer = Integer.valueOf(words[1].split("__")[1].split("_")[0]);
                int position = Integer.valueOf(words[1].split("__")[1].split("_")[1]);

                // Now we can check if it is an action
                String nameActionMethodOrPredicate = words[1].split("__")[0];
                if (nameActionMethodOrPredicate.startsWith("ACTION")) {

                    // Find the action object associate with it
                    for (Action action : problem.getActions()) {
                        if (encoder.prettyDisplayAction(action, problem).equals(nameActionMethodOrPredicate)) {

                            // Get the action ID for the decomposition
                            int actionID = encoder.GetUniqueIDForLayerAndPosition(layer, position);

                            if (layer < layerIdx) {

                                // Get the parentID of this action
                                int parentPosition = encoder.getParentPosition(layer, position);
                                int parentLayer = layer - 1;
                                int parentID = encoder.GetUniqueIDForLayerAndPosition(parentLayer, parentPosition);

                                // If the parent ID is in the actions ID, replace the parent ID with the current
                                // action
                                if (ActionsID.contains(parentID)) {
                                    ActionsID.set(ActionsID.indexOf(parentID), actionID);
                                } else {
                                    // It means the parent is a method

                                    // Count the number of actions already with this parent (because it will modify
                                    // the position of the insertion of the action)
                                    int numberActionWithThisParent = 0;
                                    for (int idx = 0; idx < MethodID.size(); idx++) {
                                        if (MethodID.get(idx) == parentID) {
                                            numberActionWithThisParent++;
                                        }
                                    }

                                    // Add it into the actions ID with the method which has generated this action
                                    ActionsID.add(actionID);
                                    MethodID.add(parentID);

                                    PlaceToInsertActionInMethod.add(
                                            hierarchy.getDecomposition().get(MethodID.get(ActionsID.indexOf(actionID)))
                                                    .size() + numberActionWithThisParent);
                                }
                            } else {

                                // Get the parentID of this action
                                int parentPosition = encoder.getParentPosition(layer, position);
                                int parentLayer = layer - 1;
                                int parentID = encoder.GetUniqueIDForLayerAndPosition(parentLayer, parentPosition);

                                // For the last layer, put the actions in order into the hierarchy
                                // If the parent ID is in the actions ID, replace the parent ID with the current
                                // action
                                if (ActionsID.contains(parentID)) {
                                    ActionsID.set(ActionsID.indexOf(parentID), actionID);
                                } else {
                                    // Add it into the actions ID
                                    ActionsID.add(actionID);
                                    MethodID.add(parentID);
                                    PlaceToInsertActionInMethod.add(hierarchy.getDecomposition()
                                            .get(MethodID.get(ActionsID.indexOf(actionID))).size());
                                }

                                // Now we can put into the hierarchy
                                hierarchy.getPrimtiveTasks().put(actionID, action);

                                // Put as well the decomposition of the method to this actionID
                                hierarchy.getDecomposition().get(MethodID.get(ActionsID.indexOf(actionID)))
                                        .add(PlaceToInsertActionInMethod.get(ActionsID.indexOf(actionID)), actionID);
                            }
                            break;
                        }
                    }
                } else if (nameActionMethodOrPredicate.startsWith("METHOD")) {

                    // Add the method to the hierarchy

                    // Find the method object associate with it
                    for (Method method : problem.getMethods()) {
                        if (encoder.prettyDisplayMethod(method, problem).equals(nameActionMethodOrPredicate)) {

                            // Get the method ID for the decomposition
                            int methodID = encoder.GetUniqueIDForLayerAndPosition(layer, position);

                            // Now add it to our hierarchy
                            hierarchy.getCounpoudTasks().put(methodID, method);
                            hierarchy.getDecomposition().put(methodID, new ArrayList<>());

                            // If the parent of this method is a initial task, the id of the initial task is
                            // given by the current position
                            // of the method
                            if (layer == 0) {
                                // hierarchy.getDecomposition().get(position).add(methodID);
                            } else {
                                // Get the parent of the method
                                int parentPosition = encoder.getParentPosition(layer, position);
                                int parentLayer = layer - 1;
                                int parentID = encoder.GetUniqueIDForLayerAndPosition(parentLayer, parentPosition);
                                hierarchy.getDecomposition().get(parentID).add(methodID);
                            }
                        }
                    }
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
     * 
     * Display debugging information about the current layer, number of clauses,
     * number of boolean and numerical variables, and the solving and encoding
     * times.
     * 
     * @param layerIdx         the index of the current layer
     * @param clauses          the clauses generated by the encoder
     * @param allBoolVariables the boolean variables generated by the encoder
     * @param allIntVariables  the numerical variables generated by the encoder
     * @param deltaEncodingTime  the encoding time for the current layer
     * @param deltaSolvingTime    the solving time for the current layer
     */
    private void displayDebuggingInfo(int layerIdx, String clauses, Vector<String> allBoolVariables, Vector<String> allIntVariables, long deltaEncodingTime, long deltaSolvingTime) {

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

        // Initialize the encoder
        TreeRexEncoder encoder = new TreeRexEncoder(problem, useSASplus);

        // Initialize the layer index and maximum number of layers
        int layerIdx = 0;
        int maxLayers = 10;

        // Initialize the variables which will store the encodning time and solving time
        long deltaEncodingTime = 0;
        long deltaSolvingTime = 0;

        // Initialize the encoding time for the initial layer
        long beginEncodeTime = System.currentTimeMillis();

        // Initialize the clauses and variables for the initial layer
        String clauses = encoder.encodeFirstLayer();
        Vector<String> allBoolVariables = encoder.getAllBoolVariables();
        Vector<String> allIntVariables = encoder.getAllIntVariables();

        int totalNumberVariables = allIntVariables.size() + allBoolVariables.size();
        LOGGER.info("Launch solver (number variables: " + totalNumberVariables + "number clauses: "
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
            responseSMT = executeSMTSolverOnFile();

            // Record the solving time
            deltaSolvingTime = System.currentTimeMillis() - beginSolveTime;
            this.getStatistics().setTimeToSearch(this.getStatistics().getTimeToSearch() + deltaSolvingTime);
    
            displayDebuggingInfo(layerIdx, clauses, allBoolVariables, allIntVariables, deltaEncodingTime, deltaSolvingTime);
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





            SequentialPlan plan = extractPlanAndHierarchyFromSolver(problem, responseSMT, encoder, layerIdx);

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
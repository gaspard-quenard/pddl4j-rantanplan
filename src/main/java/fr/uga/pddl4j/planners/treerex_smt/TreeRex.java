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
     * Write clauses into a file
     * @param clauses
     * @throws IOException
     */
    void writeIntoSMTFile(Vector<String> allBoolVariables, Vector<String> allIntVariables, String clauses) throws IOException {
        BufferedWriter writer;

        writer = new BufferedWriter(new FileWriter(this.filenameSMT));

        writer.write("(set-logic QF_LIA)\n");
        writer.write("(set-option :produce-models true)\n");

        // Declare all the variables
        for (String var: allBoolVariables) {
            writer.write("(declare-const " + var + " Bool)\n");
        }
        for (String var: allIntVariables) {
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
     * Indicate if an SMT solver has succeed to solve the SMT file
     * @param responseSolverSMT true if the SMT solver has success to solve the SMT file, false otherwise
     * @return
     */
    private Boolean fileIsSatisfiable(String responseSolverSMT) {
        return !responseSolverSMT.contains("unsat");
    }


    /**
     * TODO Problem here because, the model does not give the action in the correct order.
     * We must first get all the action true of the last layer, then reorder them in the correct order
     * and then add them to the plan
     * @param problem
     * @param outputSMTSolver
     * @param encoder
     * @param layerIdx
     * @return
     */
    private SequentialPlan extractPlanFromSolver(Problem problem, String outputSMTSolver, TreeRexEncoder encoder, int layerIdx) {

        SequentialPlan p = new SequentialPlan();
        int numberBlankActions = 0;

        // Create an array to store all the actions used for the plan
        // We cannot directly put the actions into the plan since the 
        // actions returned by the SMT solver are not necesserely in the correct order
        int size_plan = encoder.getLastLayerSize();
        Action[] planActions = new Action[size_plan];
        for (int i = 0; i < size_plan; i++) {
            planActions[i] = null;
        }

        String[] values = outputSMTSolver.split("\n");
        for (int i = 0; i < values.length; i++) {
            String s = values[i];

            if (i > 1) {
                String[] words = s.split(" ");
                if (words.length > 4) {

                    // Pass while we are not on the last layer
                    // words in the form: (define-fun METHOD_m1_go_ordering_0_f3_f0_f1_p1__3_9 () Bool false)
                    int layer = Integer.valueOf(words[1].split("__")[1].split("_")[0]);
                    if (layer < layerIdx) {
                        continue;
                    }

                    // If the value is false, we can skip as well
                    if (s.contains("true)")) {
                        // Now we can check if it is an action
                        String nameActionMethodOrPredicate = words[1].split("__")[0];
                        if (nameActionMethodOrPredicate.startsWith("ACTION")) {
                            // It is an action ! 

                            // if (nameActionMethodOrPredicate.contains("Blank")) {
                            //     // It's a blank action
                            //     numberBlankActions++;
                            //     continue;
                            // }

                            // Find the action object associate with it
                            for (Action action: problem.getActions()) {
                                if (encoder.prettyDisplayAction(action, problem).equals(nameActionMethodOrPredicate)) {
                                    int timeStep = Integer.valueOf(words[1].split("__")[1].split("_")[1]);
                                    // LOGGER.info(encoder.prettyDisplayAction(action, problem) + " " + timeStep + "\n");
                                    planActions[timeStep] = action;
                                }
                            }
                        }
                    }
                }
            }
        }
    
        int timeStep = 0;
        for (Action action: planActions) {
            if (action != null) {
                p.add(timeStep, action);
                timeStep++;
            }
        }
        return p;
    }

    /**
     * TODO Problem here because, the model does not give the action in the correct order.
     * We must first get all the action true of the last layer, then reorder them in the correct order
     * and then add them to the plan
     * @param problem
     * @param outputSMTSolver
     * @param encoder
     * @param layerIdx
     * @return
     */
    private SequentialPlan extractPlanAndHierarchyFromSolver(Problem problem, String outputSMTSolver, TreeRexEncoder encoder, int layerIdx) {

        SequentialPlan p = new SequentialPlan();
        int numberBlankActions = 0;
        Hierarchy hierarchy = new Hierarchy();

        List<Pair<Integer, Integer>> listActionsRecorded = new ArrayList<>();

        List<Integer> ActionsID = new ArrayList<>();
        List<Integer> MethodID = new ArrayList<>();

        // Add the roots tasks to the hierarchy
        int numberRootTasks = problem.getInitialTaskNetwork().getTasks().size();
        for (int rootTaskIdx = 0; rootTaskIdx < numberRootTasks; rootTaskIdx++) {
            hierarchy.getRootTasks().add(rootTaskIdx);
            hierarchy.getDecomposition().put(rootTaskIdx, new ArrayList<>());
        }

        // Create an array to store all the actions used for the plan
        // We cannot directly put the actions into the plan since the 
        // actions returned by the SMT solver are not necesserely in the correct order
        int size_plan = encoder.getLastLayerSize();
        Action[] planActions = new Action[size_plan];
        for (int i = 0; i < size_plan; i++) {
            planActions[i] = null;
        }

        String[] values = outputSMTSolver.split("\n");

        List<String> lValues = Arrays.asList(values);

        // Only keep the actions and methods which are true (do not keep blank action as well)
        lValues = Arrays.asList(lValues.stream().filter(s -> ((s.contains(" ACTION_") || s.contains(" METHOD_")) && s.contains(" true)") && !s.contains("_Blank_"))).toArray(String[]::new));

        // We also need to sort by layer and then by position
        lValues = Arrays.asList(lValues.stream().sorted(Comparator
                                    .comparingInt((String s) -> Integer.parseInt(s.split(" ")[1].split("__")[1].split("_")[0])) // Sort by layer
                                    .thenComparingInt((String s) -> Integer.parseInt(s.split(" ")[1].split("__")[1].split("_")[1])) // Sort by position in layer
                                ).toArray(String[]::new));





        for (int i = 0; i < lValues.size(); i++) {
            String s = lValues.get(i);

            String[] words = s.split(" ");
            if (words.length > 4) {

                // Pass while we are not on the last layer
                // words in the form: (define-fun METHOD_m1_go_ordering_0_f3_f0_f1_p1__3_9 () Bool false)
                int layer = Integer.valueOf(words[1].split("__")[1].split("_")[0]);
                int position = Integer.valueOf(words[1].split("__")[1].split("_")[1]);


                // Now we can check if it is an action
                String nameActionMethodOrPredicate = words[1].split("__")[0];
                if (nameActionMethodOrPredicate.startsWith("ACTION")) {

                    // Find the action object associate with it
                    for (Action action: problem.getActions()) {
                        if (encoder.prettyDisplayAction(action, problem).equals(nameActionMethodOrPredicate)) {
                            int timeStep = Integer.valueOf(words[1].split("__")[1].split("_")[1]);
                            // LOGGER.info(encoder.prettyDisplayAction(action, problem) + " " + timeStep + "\n");
                            planActions[timeStep] = action;


                            // Get the action ID for the decomposition
                            int actionID = encoder.GetUniqueIDForLayerAndPosition(layer, position);

                            if (layer < layerIdx) {

                                // Get the parentID of this action
                                int parentPosition = encoder.getParentPosition(layer, position);
                                int parentLayer = layer - 1;
                                int parentID = encoder.GetUniqueIDForLayerAndPosition(parentLayer, parentPosition);

                                // If the parent ID is in the actions ID, replace the parent ID with the current action
                                if (ActionsID.contains(parentID)) {
                                    ActionsID.set(ActionsID.indexOf(parentID), actionID);
                                } 
                                else {
                                    // Add it into the actions ID with the method which has generated this action
                                    ActionsID.add(actionID);
                                    MethodID.add(parentID);
                                }
                            } else {

                                // Get the parentID of this action
                                int parentPosition = encoder.getParentPosition(layer, position);
                                int parentLayer = layer - 1;
                                int parentID = encoder.GetUniqueIDForLayerAndPosition(parentLayer, parentPosition);

                                // For the last layer, put the actions in order into the hierarchy
                                // If the parent ID is in the actions ID, replace the parent ID with the current action
                                if (ActionsID.contains(parentID)) {
                                    ActionsID.set(ActionsID.indexOf(parentID), actionID);
                                } 
                                else {
                                    // Add it into the actions ID
                                    ActionsID.add(actionID);
                                    MethodID.add(parentID);
                                }

                                // Now we can put into the hierarchy
                                hierarchy.getPrimtiveTasks().put(actionID, action);

                                // Put as well the decomposition of the method to this actionID
                                hierarchy.getDecomposition().get(MethodID.get(ActionsID.indexOf(actionID))).add(actionID);
                            }
                            break;
                        }
                    }
                }
                else if (nameActionMethodOrPredicate.startsWith("METHOD")) {

                    // Add the method to the hierarchy

                    // Find the method object associate with it
                    for (Method method: problem.getMethods()) {
                        if (encoder.prettyDisplayMethod(method, problem).equals(nameActionMethodOrPredicate)) {  

                            // Get the method ID for the decomposition
                            int methodID = encoder.GetUniqueIDForLayerAndPosition(layer, position);

                            // Now add it to our hierarchy
                            hierarchy.getCounpoudTasks().put(methodID, method);
                            hierarchy.getDecomposition().put(methodID, new ArrayList<>());

                            // If the parent of this method is a initial task, the id of the initial task is given by the current position
                            // of the method
                            if (layer == 0) {
                                // hierarchy.getDecomposition().get(position).add(methodID);
                            }
                            else {
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
        for (Action action: hierarchy.getPrimtiveTasks().values()) {
            p.add(timeStep, action);
            timeStep++;
        }
        System.out.println(problem.toString(hierarchy));
        p.setHierarchy(hierarchy);
        
        return p;
    }


    /**
     * Search a solution plan to a specific domain using a SMT solver (cvc5).
     *
     * @param problem the problem to solve.
     * @return the plan found or null if no plan was found.
     */
    @Override
    public Plan solve(Problem problem) {

        boolean useSASplus = true;

        long beginEncodeTime = System.currentTimeMillis();
        TreeRexEncoder encoder = new TreeRexEncoder(problem, useSASplus);

        // Encode 
        // encoder.Encode();

        LOGGER.info("Encode layer 0\n");

        String clauses = encoder.encodeFirstLayer();
        Vector<String> allBoolVariables = encoder.getAllBoolVariables(); 
        Vector<String> allIntVariables = encoder.getAllIntVariables(); 
        int layerIdx = 0;

        // Write those clause and variables to a file 
        try {
            writeIntoSMTFile(allBoolVariables, allIntVariables, clauses);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        long endEncodeTime = System.currentTimeMillis();
        this.getStatistics()
                .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

        // Try to solve the SMT file
        long beginSolveTime = System.currentTimeMillis();
        int totalNumberVariables = allIntVariables.size() + allBoolVariables.size();
        LOGGER.info("Launch solver (number variables: " + totalNumberVariables + " number clauses: " + clauses.split("\n").length + "\n");
        String responseSolver = executeSMTSolverOnFile();
        long endSolveTime = System.currentTimeMillis();
        this.getStatistics()
                .setTimeToSearch(this.getStatistics().getTimeToSearch() + (endSolveTime - beginSolveTime));

        Boolean fileIsSatisfiable = fileIsSatisfiable(responseSolver);

        // Should not happen
        if (fileIsSatisfiable) {
            System.out.println("SUCCESS !");
        } else {
            LOGGER.info("File is not satisfiable\n");
        }

        // A safe variable
        int maxLayer = 15;

        while (!fileIsSatisfiable && layerIdx < maxLayer) {

            beginEncodeTime = System.currentTimeMillis();

            // Increment the layer idx
            layerIdx++;

            System.out.println("Encode for layer " + layerIdx);

            // Get the new clauses
            clauses = encoder.encodeNextLayer(layerIdx);
            allBoolVariables = encoder.getAllBoolVariables();
            allIntVariables = encoder.getAllIntVariables();

            // Write the clauses and variables to a file
            try {
                writeIntoSMTFile(allBoolVariables, allIntVariables, clauses);
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            endEncodeTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

            beginSolveTime = System.currentTimeMillis();
            totalNumberVariables = allIntVariables.size() + allBoolVariables.size();
            LOGGER.info("Launch solver (number variables: " + totalNumberVariables + " number clauses: " + clauses.split("\n").length + ")\n");
            responseSolver = executeSMTSolverOnFile();
            endSolveTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToSearch(this.getStatistics().getTimeToSearch() + (endSolveTime - beginSolveTime));
            if (fileIsSatisfiable(responseSolver)) {
                System.out.println("File is satisfiable !");
                // Extract plan from response
                SequentialPlan plan = extractPlanAndHierarchyFromSolver(problem, responseSolver, encoder, layerIdx);

                // Check if plan is valid
                try {
                    LOGGER.info("Check if plan is valid with VAL...\n");
                    Boolean planIsValid = this.validatePlan(problem, plan);
                    if (planIsValid) {
                        LOGGER.info("Plan is valid\n");
                        return plan;
                    }
                    else {
                        LOGGER.error("Plan is not valid !\n");
                        return null;
                    }
                    
                } catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
                System.out.println("Time to encode: " + this.getStatistics().getTimeToEncode() + " ms");
                System.out.println("Time to search: " + this.getStatistics().getTimeToSearch() + " ms");
                return plan;
            }
            else {
                System.out.println("File is not satisfiable. Increase the layer by 1");
            }
        }

        LOGGER.error("Failed to solve the SMT file !\n");
        return null;
    }

    Boolean validatePlan(Problem problem, Plan plan) throws IOException {


        // Write the hierarchy of the plan to a file
        String filenamePlan = "tmp_plan.txt";

        BufferedWriter writer = new BufferedWriter(new FileWriter(filenamePlan));

        writer.write(problem.toString(plan.getHierarchy()));
        writer.close();


        String outputVAL = "";
        String command = "./" + this.path_exec_VAL + " --verify " + this.getDomain() + " " + this.getProblem() + " " + filenamePlan;
        try {
            Process p = Runtime.getRuntime().exec(command);
            BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String newLine = "";

            while ((newLine = reader.readLine()) != null) {
                outputVAL += newLine + "\n";
            }
            p.waitFor();
        } catch (IOException | InterruptedException e1) {
            e1.printStackTrace();
        }

        // Get the last line which indicate if the plan if valid
        String[] lines = outputVAL.split("\n");
        String lastLine = lines[lines.length - 1];

        // The last line should contains the string "Plan verification result". If it is not the case, it means that 
        // the execuate used or the arguments given are incorrect
        if (!lastLine.contains("Plan verification result")) {
            LOGGER.error("Cannot verify the plan given. Output returned by executable: \n" + outputVAL);
            return false;
        }
        // The last line should contains the string true if the plan is correct
        return lastLine.contains("true");
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
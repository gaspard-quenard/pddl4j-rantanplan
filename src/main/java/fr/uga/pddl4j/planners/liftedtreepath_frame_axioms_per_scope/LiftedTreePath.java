package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

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

@CommandLine.Command(name = "LiftedTreePath", version = "LiftedTreePath 0.1", description = "Solves a specified classical problem using SMT encoding.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")
public class LiftedTreePath extends AbstractHTNPlanner {

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(LiftedTreePath.class.getName());

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
        // long beginComputeSASplus = System.currentTimeMillis();
        // System.out.println("Start to determinate lifted fam mutex..");
        // SASplusLiftedFamGroup.determinateLiftedFamGroups(pb);
        // long deltabeginComputeSASplus = System.currentTimeMillis() - beginComputeSASplus;
        // System.out.println("Time to compute mutex: " + deltabeginComputeSASplus + " ms");
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


        // Initialize the variables which will store the encoding time and solving time
        long deltaInitializingTreePathTime = 0;
        long deltaEncodingTime = 0;
        long deltaSolvingTime = 0;

        long beginInitializeTreePathTime = System.currentTimeMillis();

        // Initialize the encoder
        LiftedTreePathEncoder encoder = new LiftedTreePathEncoder(problem, this.getDomain(), this.getProblem());

        // Record the encoding time for the initial layer
        deltaInitializingTreePathTime = System.currentTimeMillis() - beginInitializeTreePathTime;

        LOGGER.info("Initializing tree path time: " + deltaInitializingTreePathTime + " ms.\n");

        // Initialize the layer index and maximum number of layers
        int layerIdx = 0;
        int maxLayers = 15;


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
            final LiftedTreePath planner = new LiftedTreePath();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }
}
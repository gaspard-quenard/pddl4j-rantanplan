package fr.uga.pddl4j.planners.treerex_smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Vector;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.io.InputStreamReader;

import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.planners.htn.stn.AbstractSTNPlanner;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.util.BitVector;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import picocli.CommandLine;

@CommandLine.Command(name = "TreeRex", version = "TreeRex 0.1", description = "Solves a specified classical problem using SMT encoding.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")
public class TreeRex extends AbstractSTNPlanner {

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(TreeRex.class.getName());

    private String path_exec_VAL = "src/test/resources/validators/validate-nux";

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
    void writeIntoSMTFile(Vector<String> allVariables, String clauses) throws IOException {
        BufferedWriter writer;

        writer = new BufferedWriter(new FileWriter(this.filenameSMT));

        writer.write("(set-logic QF_LIA)\n");
        writer.write("(set-option :produce-models true)\n");

        // Declare all the variables
        for (String var: allVariables) {
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
                                    p.add(timeStep, action);
                                }
                            }
                        }
                    }
                }
            }
        }
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

        long beginEncodeTime = System.currentTimeMillis();
        TreeRexEncoder encoder = new TreeRexEncoder(problem);

        // Encode 
        // encoder.Encode();

        LOGGER.info("Encode layer 0\n");

        String clauses = encoder.encodeFirstLayer();
        Vector<String> allVariables = encoder.getAllVariables(); 
        int layerIdx = 0;

        // Write those clause and variables to a file 
        try {
            writeIntoSMTFile(allVariables, clauses);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        long endEncodeTime = System.currentTimeMillis();
        this.getStatistics()
                .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

        // Try to solve the SMT file
        long beginSolveTime = System.currentTimeMillis();
        LOGGER.info("Launch solver\n");
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
        int maxLayer = 20;

        while (!fileIsSatisfiable && layerIdx < maxLayer) {

            beginEncodeTime = System.currentTimeMillis();

            // Increment the layer idx
            layerIdx++;

            System.out.println("Encode for layer " + layerIdx);

            // Get the new clauses
            clauses = encoder.encodeNextLayer(layerIdx);
            allVariables = encoder.getAllVariables();

            // Write the clauses and variables to a file
            try {
                writeIntoSMTFile(allVariables, clauses);
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            endEncodeTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

            beginSolveTime = System.currentTimeMillis();
            LOGGER.info("Launch solver\n");
            responseSolver = executeSMTSolverOnFile();
            endSolveTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToSearch(this.getStatistics().getTimeToSearch() + (endSolveTime - beginSolveTime));
            if (fileIsSatisfiable(responseSolver)) {
                System.out.println("File is satisfiable !");
                // Extract plan from response
                SequentialPlan plan = extractPlanFromSolver(problem, responseSolver, encoder, layerIdx);

                // Check if plan is valid
                // try {
                //     LOGGER.info("Check if plan is valid with VAL...\n");
                //     Boolean planIsValid = this.validatePlan(problem, plan);
                //     if (planIsValid) {
                //         LOGGER.info("Plan is valid\n");
                //         return plan;
                //     }
                //     else {
                //         LOGGER.error("Plan is not valid !\n");
                //         return null;
                //     }
                    
                // } catch (IOException e) {
                //     // TODO Auto-generated catch block
                //     e.printStackTrace();
                // }
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


        // Write the plan to tmp file
        String filenamePlan = "tmp_plan";

        BufferedWriter writer = new BufferedWriter(new FileWriter(filenamePlan));

        writer.write(problem.toString(plan));
        writer.close();


        String outputVAL = "";
        String command = "./" + path_exec_VAL + " " + this.getDomain() + " " + this.getProblem() + " " + filenamePlan;
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

        return outputVAL.contains("Plan valid");
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
package fr.uga.pddl4j.planners.rantanplan;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Vector;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.io.InputStreamReader;

import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
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

@CommandLine.Command(name = "Rantanplan", version = "Rantanplan 0.1", description = "Solves a specified classical problem using SMT encoding.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")
public class Rantanplan extends AbstractPlanner {

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(Rantanplan.class.getName());

    private String[] lifted_actions;
    private String[] lifted_predicates;
    private String[] lifted_binary_encoding_temp_variables;
    private String[] lifted_actions_t_implies_precondition_t;
    private String[] lifted_actions_t_implies_effects_t_plus_1;
    private String[] lifted_explanatory_frame_axioms;
    private String lifted_at_least_one_action;
    private String lifted_at_most_one_action;
    private String lifted_goal_state;

    private Vector<Term> vectorTerms;

    private String path_exec_VAL = "src/test/resources/validators/validate-nux";

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
     * Return a string containing an action in easily readable format
     * 
     * @param a       The action to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the action in easily readable format
     */
    private String prettyDisplayAction(Action a, Problem problem) {
        StringBuilder actionToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        actionToDisplay.append(a.getName());

        // Then, for each argument of this fluent, add the argument into the string
        for (int actionArg : a.getInstantiations()) {
            actionToDisplay.append("_" + problem.getConstantSymbols().get(actionArg));
        }

        return actionToDisplay.toString();
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
        fluentToDisplay.append(problem.getPredicateSymbols().get(f.getSymbol()));

        // Then, for each argument of this fluent, add the argument into the string
        for (int fluentArg : f.getArguments()) {
            fluentToDisplay.append("_" + problem.getConstantSymbols().get(fluentArg));
        }

        return fluentToDisplay.toString();
    }

    private String prettyDisplayBinaryVar(int nValue) {
        return "temp_binary_enc" + Integer.toString(nValue);
    }

    private String convertNumbertoBinaryStringOfSize(int number, int size) {
        String encodingSize = "%" + size + "s";
        return String.format(encodingSize, Integer.toBinaryString(number)).replaceAll(" ", "0");
    }

    private String lift_to_time_t(String fluentOrAction) {
        return fluentOrAction + "__@";
    }

    private String groundToTS(String liftPredicateOrAction, int ts) {
        // LOGGER.info(liftPredicateOrAction + "\n");
        return liftPredicateOrAction.replace("@", Integer.toString(ts)).replace("#", Integer.toString(ts + 1));
    }

    private String lift_to_time_t_plus_1(String fluentOrAction) {
        return fluentOrAction + "__#";
    }

    private String[] encode_lifted_actions(Problem problem) {
        String[] liftActions = new String[problem.getActions().size()];

        for (int idxAction = 0; idxAction < problem.getActions().size(); idxAction++) {
            Action a = problem.getActions().get(idxAction);
            liftActions[idxAction] = lift_to_time_t(prettyDisplayAction(a, problem));
        }
        return liftActions;
    }

    private String[] encode_lifted_predicates(Problem problem) {
        String[] liftPredicates = new String[problem.getFluents().size()];

        for (int idxPredicate = 0; idxPredicate < problem.getFluents().size(); idxPredicate++) {
            Fluent f = problem.getFluents().get(idxPredicate);
            liftPredicates[idxPredicate] = lift_to_time_t(prettyDisplayFluent(f, problem));
        }
        return liftPredicates;
    }

    /**
     * Encode in a lifted way all the predicate of type: Action_t => PrecontAction_t
     * 
     * @param problem The problem to solve
     * @return Array containing all the predicates of type Action_t =>
     *         PrecontAction_t in a lifted way
     */
    private String[] encode_lifted_actions_t_implies_preconditions_t(Problem problem) {

        int size_array = problem.getActions().size();
        String[] lifted_actions_t_implies_precondition_t = new String[size_array];

        int lifted_actions_idx = 0;

        for (Action action : problem.getActions()) {
            StringBuilder lifted_action_t_implies_precondition_t = new StringBuilder("=> ");
            lifted_action_t_implies_precondition_t.append(lift_to_time_t(prettyDisplayAction(action, problem)));

            lifted_action_t_implies_precondition_t.append(" ( and ");

            BitVector precondPos = action.getPrecondition().getPositiveFluents();
            for (int p = precondPos.nextSetBit(0); p >= 0; p = precondPos.nextSetBit(p + 1)) {
                Fluent f = problem.getFluents().get(p);
                String fluentVar = prettyDisplayFluent(f, problem);
                lifted_action_t_implies_precondition_t.append(lift_to_time_t(fluentVar) + " ");
            }

            BitVector precondNeg = action.getPrecondition().getNegativeFluents();
            for (int p = precondNeg.nextSetBit(0); p >= 0; p = precondNeg.nextSetBit(p + 1)) {
                Fluent f = problem.getFluents().get(p);
                String fluentVar = prettyDisplayFluent(f, problem);
                lifted_action_t_implies_precondition_t.append("( not " + lift_to_time_t(fluentVar) + " ) ");
            }

            lifted_action_t_implies_precondition_t.append(")");
            // System.out.println("(Action impl preconds lifted): " + lifted_action_t_implies_precondition_t);

            lifted_actions_t_implies_precondition_t[lifted_actions_idx] = lifted_action_t_implies_precondition_t
                    .toString();
            lifted_actions_idx++;
        }

        return lifted_actions_t_implies_precondition_t;
    }

    /**
     * Encode in a lifted way all the predicate of type: Action_t => Effect_t_plus_1
     * Do not consider conditional effects yet
     * 
     * @param problem The problem to solve
     * @return Array containing all the predicates of type Action_t =>
     *         EffectsAction_t_plus_1 in a lifted way
     */
    private String[] encode_lifted_actions_t_implies_effects_t_plus_1(Problem problem) {

        int size_array = problem.getActions().size();
        String[] lifted_actions_t_implies_effects_t_plus_1 = new String[size_array];

        int lifted_actions_idx = 0;

        for (Action action : problem.getActions()) {
            StringBuilder lifted_action_t_implies_effects_t_plus_1 = new StringBuilder("=> ");
            lifted_action_t_implies_effects_t_plus_1.append(lift_to_time_t(prettyDisplayAction(action, problem)));

            lifted_action_t_implies_effects_t_plus_1.append(" ( and ");

            BitVector precondPos = action.getUnconditionalEffect().getPositiveFluents();
            for (int p = precondPos.nextSetBit(0); p >= 0; p = precondPos.nextSetBit(p + 1)) {
                Fluent f = problem.getFluents().get(p);
                String fluentVar = prettyDisplayFluent(f, problem);
                lifted_action_t_implies_effects_t_plus_1.append(lift_to_time_t_plus_1(fluentVar) + " ");
            }

            BitVector precondNeg = action.getUnconditionalEffect().getNegativeFluents();
            for (int p = precondNeg.nextSetBit(0); p >= 0; p = precondNeg.nextSetBit(p + 1)) {
                Fluent f = problem.getFluents().get(p);
                String fluentVar = prettyDisplayFluent(f, problem);
                lifted_action_t_implies_effects_t_plus_1.append("( not " + lift_to_time_t_plus_1(fluentVar) + ") ");
            }

            lifted_action_t_implies_effects_t_plus_1.append(")");
            // System.out.println("(Action impl effects lifted): " + lifted_action_t_implies_effects_t_plus_1);

            lifted_actions_t_implies_effects_t_plus_1[lifted_actions_idx] = lifted_action_t_implies_effects_t_plus_1
                    .toString();
            lifted_actions_idx++;
        }

        return lifted_actions_t_implies_effects_t_plus_1;
    }

    /**
     * Encode in a lifted way the explanatory frame axioms (p_t ^ not(p_t+1) =>
     * action_which_modify_p__t)
     * 
     * @param problem The problem to solve
     * @return Array containing all the explanatory frame axioms in a lifted way
     */
    private String[] encode_lifted_explanatory_frame_axioms(Problem problem) {

        // For each predicate, find all the actions which have it as a positive effects
        // and all the actions which have it as a negative effects
        ArrayList<Action>[] positiveEffectOnFluent = (ArrayList<Action>[]) new ArrayList[problem.getFluents().size()];
        ArrayList<Action>[] negativeEffectOnFluent = (ArrayList<Action>[]) new ArrayList[problem.getFluents().size()];

        for (int i = 0; i < problem.getFluents().size(); i++) {
            positiveEffectOnFluent[i] = new ArrayList<Action>();
            negativeEffectOnFluent[i] = new ArrayList<Action>();
        }

        for (Action action : problem.getActions()) {
            BitVector effectPos = action.getUnconditionalEffect().getPositiveFluents();

            for (int p = effectPos.nextSetBit(0); p >= 0; p = effectPos.nextSetBit(p + 1)) {
                positiveEffectOnFluent[p].add(action);
                effectPos.set(p);
            }

            BitVector effectNeg = action.getUnconditionalEffect().getNegativeFluents();

            for (int p = effectNeg.nextSetBit(0); p >= 0; p = effectNeg.nextSetBit(p + 1)) {
                negativeEffectOnFluent[p].add(action);
                effectNeg.set(p);
            }
        }

        // Calculate number lifted explanatory frame axioms
        int number_lifted_explanatory_frame_axioms = 0;
        for (int stateIdx = 0; stateIdx < problem.getFluents().size(); stateIdx++) {
            if (negativeEffectOnFluent[stateIdx].size() != 0) {
                number_lifted_explanatory_frame_axioms++;
            }
            if (positiveEffectOnFluent[stateIdx].size() != 0) {
                number_lifted_explanatory_frame_axioms++;
            }
        }

        String[] lifted_explanatory_frame_axioms = new String[number_lifted_explanatory_frame_axioms];
        int idx = 0;

        // Now, we can construct the explanatory frame axioms
        for (int stateIdx = 0; stateIdx < problem.getFluents().size(); stateIdx++) {

            if (negativeEffectOnFluent[stateIdx].size() != 0) {

                StringBuilder lifted_explanatory_frame_axiom = new StringBuilder("=> ");
                Fluent f = problem.getFluents().get(stateIdx);
                String fluentVar = prettyDisplayFluent(f, problem);
                lifted_explanatory_frame_axiom.append(
                        "( and " + lift_to_time_t(fluentVar) + " ( not " + lift_to_time_t_plus_1(fluentVar)
                                + " ) ) ( or ");

                for (Action action : negativeEffectOnFluent[stateIdx]) {
                    lifted_explanatory_frame_axiom.append(lift_to_time_t(prettyDisplayAction(action, problem)) + " ");
                }

                lifted_explanatory_frame_axiom.append(")");

                // System.out.println("(explantory frame axiom: " + lifted_explanatory_frame_axiom);

                lifted_explanatory_frame_axioms[idx] = lifted_explanatory_frame_axiom.toString();
                idx++;
            }

            if (positiveEffectOnFluent[stateIdx].size() != 0) {
                StringBuilder lifted_explanatory_frame_axiom = new StringBuilder("=> ");
                Fluent f = problem.getFluents().get(stateIdx);
                String fluentVar = prettyDisplayFluent(f, problem);
                lifted_explanatory_frame_axiom.append(
                        "( and ( not " + lift_to_time_t(fluentVar) + " ) " + lift_to_time_t_plus_1(fluentVar)
                                + " ) ( or ");

                for (Action action : positiveEffectOnFluent[stateIdx]) {
                    lifted_explanatory_frame_axiom.append(lift_to_time_t(prettyDisplayAction(action, problem)) + " ");
                }

                lifted_explanatory_frame_axiom.append(")");

                // System.out.println("(explantory frame axiom: " + lifted_explanatory_frame_axiom);

                lifted_explanatory_frame_axioms[idx] = lifted_explanatory_frame_axiom.toString();
                idx++;
            }
        }

        return lifted_explanatory_frame_axioms;
    }

    /**
     * Encode in a lifted way the at_least_one_action__t
     * 
     * @param problem The problem to solve
     * @return Array containing the predicate for at_least_one_action in a lifted
     *         way
     */
    private String encode_lifted_at_least_one_action(Problem problem) {

        StringBuilder lifted_at_least_one_action = new StringBuilder(" or ");
        for (Action action : problem.getActions()) {
            lifted_at_least_one_action.append(lift_to_time_t(prettyDisplayAction(action, problem)) + " ");
        }

        return lifted_at_least_one_action.toString();
    }

    private String[] encode_lifted_binary_encoding_temp_variables(Problem problem) {

        int numberActions = problem.getActions().size();
        int numberTempVariableToCreate = (int) Math.ceil(Math.log(numberActions) / Math.log(2));

        String[] lifted_binary_encoding_temp_variables = new String[numberTempVariableToCreate];

        for (int i = 0; i < numberTempVariableToCreate; i++) {
            lifted_binary_encoding_temp_variables[i] = lift_to_time_t("temp_binary_enc" + Integer.toString(i));
            ;
        }

        return lifted_binary_encoding_temp_variables;
    }

    /**
     * Encode in a lifted way the at_most_one_action__t
     * 
     * @param problem The problem to solve
     * @return Array containing the predicate for at_most_one_action in a lifted way
     */
    private String encode_lifted_at_most_one_action(Problem problem) {

        // Should get the temp binary variable here from somewhere since
        // we also need to declare them to the SMT solver

        int numberActions = problem.getActions().size();

        int numberTempVariables = this.lifted_binary_encoding_temp_variables.length;

        StringBuilder lifted_full_at_most_action = new StringBuilder(" and ");

        for (int idxAction = 0; idxAction < problem.getActions().size(); idxAction++) {
            Action a = problem.getActions().get(idxAction);
            String binaryValueOfIdxAction = convertNumbertoBinaryStringOfSize(idxAction, numberTempVariables);
            for (int i = 0; i < binaryValueOfIdxAction.length(); i++) {
                String lifted_at_most_one_action;
                if (binaryValueOfIdxAction.charAt(i) == '1') {
                    lifted_at_most_one_action = String.format("( or ( not %s ) %s ) ",
                            lift_to_time_t(prettyDisplayAction(a, problem)),
                            this.lifted_binary_encoding_temp_variables[i]);
                } else {
                    lifted_at_most_one_action = String.format("( or ( not %s ) ( not %s ) ) ",
                            lift_to_time_t(prettyDisplayAction(a, problem)),
                            this.lifted_binary_encoding_temp_variables[i]);
                }
                // System.out.println("(at most one action): " + lifted_at_most_one_action);
                lifted_full_at_most_action.append(lifted_at_most_one_action);
            }
        }

        // lifted_full_at_most_action.append(")");

        return lifted_full_at_most_action.toString();
    }

    private String encode_lifted_goal_state(Problem problem) {

        // Get the bit vector that contains all the fluents at the goal state
        BitVector goalPosFluents = problem.getGoal().getPositiveFluents();
        StringBuilder lifted_goal_state = new StringBuilder(" and ");

        for (int p = goalPosFluents.nextSetBit(0); p >= 0; p = goalPosFluents.nextSetBit(p + 1)) {
            Fluent f = problem.getFluents().get((int) p);
            lifted_goal_state.append(lift_to_time_t(prettyDisplayFluent(f, problem)) + " ");
            goalPosFluents.set(p);
        }

        return lifted_goal_state.toString();
    }

    private String declareConstantsForTS(int ts) {

        StringBuilder allConstantsForTs = new StringBuilder();
        for (String lifted_action : this.lifted_actions) {
            allConstantsForTs.append("(declare-const " + groundToTS(lifted_action, ts) + " Bool)\n");
        }
        for (String lifted_predicate : this.lifted_predicates) {
            allConstantsForTs.append("(declare-const " + groundToTS(lifted_predicate, ts) + " Bool)\n");
        }
        for (String lifted_temp_var : this.lifted_binary_encoding_temp_variables) {
            allConstantsForTs.append("(declare-const " + groundToTS(lifted_temp_var, ts) + " Bool)\n");
        }

        return allConstantsForTs.toString();
    }

    private void declareConstantsForTSCVC5(int ts, Solver solver) {

        Sort boolSort = solver.getBooleanSort();

        for (String lifted_action : this.lifted_actions) {
            Term t = solver.mkConst(boolSort, groundToTS(lifted_action, ts));
            vectorTerms.add(t);
        }
        for (String lifted_predicate : this.lifted_predicates) {
            Term t = solver.mkConst(boolSort, groundToTS(lifted_predicate, ts));
            vectorTerms.add(t);
        }
        for (String lifted_temp_var : this.lifted_binary_encoding_temp_variables) {
            Term t = solver.mkConst(boolSort, groundToTS(lifted_temp_var, ts));
            vectorTerms.add(t);
        }
    }

    private String executeSMTSolverOnFile(String filenameSMT) {
        String outputSMTSolver = "";
        String executableSolverSMT = "cvc5";
        String command = "./" + executableSolverSMT + " " + filenameSMT + " --lang smt";
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

    private Boolean fileIsSatisfiable(String responseSolverSMT) {
        return !responseSolverSMT.contains("unsat");
    }


    private SequentialPlan extractPlanFromSolver(Problem problem, String outputSMTSolver) {

        SequentialPlan p = new SequentialPlan();

        // Get all actions name
        String[] allActionsName = new String[this.lifted_actions.length];
        for (int i = 0; i < this.lifted_actions.length; i++) {
            allActionsName[i] = this.lifted_actions[i].split("__")[0];
        }

        String[] values = outputSMTSolver.split("\n");
        for (int i = 0; i < values.length; i++) {
            String s = values[i];

            if (i > 1) {
                String[] words = s.split(" ");
                if (words.length > 4) {

                    // Let's see if this is an action
                    String nameActionOfPredicate = words[1].split("__")[0];
                    int timeStep = Integer.valueOf(words[1].split("__")[1]);
                    if (Arrays.stream(allActionsName).anyMatch(nameActionOfPredicate::equals))
                    {
                        if (s.contains("true")) {
                            // System.out.println("Action " + nameActionOfPredicate + " is true for timestep " + timeStep);
                            // Get the action associate with this name
                            for (Action action: problem.getActions()) {
                                if (prettyDisplayAction(action, problem).equals(nameActionOfPredicate)) {
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
     * Use https://www.lri.fr/~conchon/TER/2013/2/SMTLIB2.pdf to see format of SMT
     * formula
     * 
     * @param problem
     * @return
     * @throws IOException
     */
    private SequentialPlan writeSMTFile(Problem problem) throws IOException {
        // Initialize the file
        BufferedWriter writer;
        String filename = "test.SMT";

        long beginEncodeTime = System.currentTimeMillis();

        StringBuilder fileToWrite = new StringBuilder();

        writer = new BufferedWriter(new FileWriter(filename));

        StringBuilder constrainsConstants = new StringBuilder();
        StringBuilder constrainsInitState = new StringBuilder();
        StringBuilder constrainsPrecondsAction = new StringBuilder();
        StringBuilder constrainsEffectsAction = new StringBuilder();
        StringBuilder constrainsExplanatoryFrameAxioms = new StringBuilder();
        StringBuilder constrainsAtLeastOneAction = new StringBuilder();
        StringBuilder constrainsAtMostOneAction = new StringBuilder();
        StringBuilder constrainsGoalState = new StringBuilder();

        StringBuilder constrainsActionsUsedAtLeastOnce = new StringBuilder();


        // Write the constants for time step = 0
        String constantsAtTS_0 = declareConstantsForTS(0);

        constrainsConstants.append("; Constants for ts 0\n");
        constrainsConstants.append(constantsAtTS_0);



        // Write as well the initial state
        constrainsInitState.append("; Init state\n");
        BitVector initPredicatePos = problem.getInitialState().getPositiveFluents();

        HashSet<Integer> fluentsNotInInitState = new HashSet<Integer>();
        for (int i = 0; i < problem.getFluents().size(); i++) {
            fluentsNotInInitState.add(i);
        }

        for (int p = initPredicatePos.nextSetBit(0); p >= 0; p = initPredicatePos.nextSetBit(p + 1)) {
            Fluent f = problem.getFluents().get(p);
            constrainsInitState.append("(assert (= " + groundToTS(lift_to_time_t(prettyDisplayFluent(f, problem)), 0) + " true))\n");
            fluentsNotInInitState.remove(p);
            initPredicatePos.set(p);
        }

        for (Integer predicateNotInInitState : fluentsNotInInitState) {
            Fluent f = problem.getFluents().get(predicateNotInInitState);
            constrainsInitState.append("(assert (= " + groundToTS(lift_to_time_t(prettyDisplayFluent(f, problem)), 0) + " false))\n");
        }

        Boolean modelIsFound = false;
        int sizePlanToSearchFor = 1;
        int safe_check = 0;
        while (!modelIsFound && safe_check < 50) {

            System.out.println("Encode plan of size " + sizePlanToSearchFor);

            if (sizePlanToSearchFor > 1) {
                writer.close();
                // Remove the last 4 lines of the file. Which contains a comment, the goal state
                // (which will change),
                // and the lines check-sat get-model and exit
                // RandomAccessFile f = new RandomAccessFile("test.SMT", "rw");
                // int remaining_line_to_delete = 5;
                // long length = f.length() - 1;
                // byte b;
                // while (remaining_line_to_delete > 0) {
                //     do {
                //         length -= 1;
                //         f.seek(length);
                //         b = f.readByte();
                //     } while (b != '\n');
                //     remaining_line_to_delete -= 1;
                // }
                // f.setLength(length + 1);
                // f.close();

                // Remove the last five lines of file to write
                
                // int remaining_line_to_delete = 5;
                // while (remaining_line_to_delete > 0) {
                //     if (fileToWrite.charAt(fileToWrite.length() - 1) == '\n') {
                //         remaining_line_to_delete -= 1;
                //     }
                //     fileToWrite.setLength(fileToWrite.length() - 1);
                // }

                fileToWrite.setLength(0);
                constrainsActionsUsedAtLeastOnce.setLength(0);
                

                writer = new BufferedWriter(new FileWriter("test.SMT"));
            }

            int currentTimeStep = sizePlanToSearchFor - 1;
            int nextTimeStep = sizePlanToSearchFor;

            String constantsAtTS = declareConstantsForTS(nextTimeStep);
            constrainsConstants.append("; Declare constants for ts " + Integer.toString(nextTimeStep) + "\n");
            constrainsConstants.append(constantsAtTS);

            // Write actions_t_implies_precondition_t
            constrainsPrecondsAction.append("; action_t implies precond_t for ts " + Integer.toString(currentTimeStep) + "\n");
            for (String act_implies_preconf : this.lifted_actions_t_implies_precondition_t) {
                constrainsPrecondsAction.append("(assert (" + groundToTS(act_implies_preconf, currentTimeStep) + "))\n");
            }

            // Write actions_t_implies_effects_t_plus_1
            constrainsEffectsAction.append("; actions_t_implies_effects_t_plus_1 for ts " + Integer.toString(currentTimeStep) + "\n");
            for (String act_implies_effects : this.lifted_actions_t_implies_effects_t_plus_1) {
                constrainsEffectsAction.append("(assert (" + groundToTS(act_implies_effects, currentTimeStep) + "))\n");
            }

            // Write the explanatory frame axioms for this timestep
            constrainsExplanatoryFrameAxioms.append("; explanatory frame axioms for ts " + Integer.toString(currentTimeStep) + "\n");
            for (String explanatory_frame_axiom : this.lifted_explanatory_frame_axioms) {
                constrainsExplanatoryFrameAxioms.append("(assert (" + groundToTS(explanatory_frame_axiom, currentTimeStep) + "))\n");
            }

            // Write the at least one action
            constrainsAtLeastOneAction.append("; at least one action for ts " + Integer.toString(currentTimeStep) + "\n");
            constrainsAtLeastOneAction.append("(assert (" + groundToTS(this.lifted_at_least_one_action, currentTimeStep) + "))\n");

            // Write the at most one action
            constrainsAtMostOneAction.append("; at most one action for ts " + Integer.toString(currentTimeStep) + "\n");
            constrainsAtMostOneAction.append("(assert (" + groundToTS(this.lifted_at_most_one_action, currentTimeStep) + "))\n");

            // Now, we need to add retractable goal state + retractable line check-sat +
            // retractable line exit
            constrainsGoalState.setLength(0);
            constrainsGoalState.append("; Goal state for ts " + Integer.toString(nextTimeStep) + "\n");
            constrainsGoalState.append("(assert (" + groundToTS(this.lifted_goal_state, nextTimeStep) + "))\n");
            ////////// TEST ////////////

            
            // String[] actionsUseAtLeastOnce = {
            //     "pick-up_d", 
            //     "pick-up_f",
            //     "put-down_g", 
            //     "stack_a_c", 
            //     "stack_b_f", 
            //     "stack_d_a", 
            //     "stack_e_b", 
            //     "stack_f_d", 
            //     "unstack_a_d", 
            //     "unstack_b_c",
            //     "unstack_e_f",
            //     "unstack_g_e"}; 
                

            // for (String actionUsedAtLeastOnce: actionsUseAtLeastOnce) {
            //     StringBuilder constraint = new StringBuilder("(assert (or ");
            //     for (int i = 0; i < currentTimeStep + 1; i++) {
            //         constraint.append(groundToTS(lift_to_time_t(actionUsedAtLeastOnce), i) + " ");
            //     }
            //     constraint.append("))\n");
            //     // LOGGER.info(constraint.toString());
            //     constrainsActionsUsedAtLeastOnce.append(constraint.toString());
            // }

            ///////// END TEST /////////

            // Write all constrains to file
            fileToWrite.setLength(0);
            fileToWrite.append("(set-option :produce-models true)\n");
            fileToWrite.append("(set-logic QF_LIA)\n");

            fileToWrite.append(constrainsConstants);
            fileToWrite.append(constrainsInitState);
            // fileToWrite.append(constrainsActionsUsedAtLeastOnce);
            fileToWrite.append(constrainsPrecondsAction);
            fileToWrite.append(constrainsEffectsAction);
            fileToWrite.append(constrainsExplanatoryFrameAxioms);
            fileToWrite.append(constrainsAtLeastOneAction);
            fileToWrite.append(constrainsAtMostOneAction);
            fileToWrite.append(constrainsGoalState);

            fileToWrite.append("(check-sat)\n");
            fileToWrite.append("(get-model)\n");
            fileToWrite.append("(exit)\n");


            writer.write(fileToWrite.toString());
            writer.flush();

            System.out.println("Launch solver on problem encoded");
            long endEncodeTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

            long beginSolveTime = System.currentTimeMillis();
            String responseSolver = executeSMTSolverOnFile(filename);
            long endSolveTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToSearch(this.getStatistics().getTimeToSearch() + (endSolveTime - beginSolveTime));
            if (fileIsSatisfiable(responseSolver)) {
                System.out.println("File is satisfiable !");
                // Extract plan from response
                SequentialPlan plan = extractPlanFromSolver(problem, responseSolver);
                return plan;
            }
            else {
                System.out.println("File is not satisfiable ");
                // Check sat here
                safe_check++;
                sizePlanToSearchFor++;
                beginEncodeTime = System.currentTimeMillis();
            }
        }

        writer.close();

        return null;
    }

    private SequentialPlan encodeToCVC5(Problem problem) throws IOException, CVC5ApiException {

        this.vectorTerms = new Vector<Term>();
        try (Solver solver = new Solver())
        {
            solver.setOption("produce-models", "true");
            
            solver.setLogic("QF_LIA");

            Sort boolSort = solver.getBooleanSort();

            // Declare constants for ts 0
            declareConstantsForTSCVC5(0, solver);

            // Write as well the initial state
            BitVector initPredicatePos = problem.getInitialState().getPositiveFluents();

            HashSet<Integer> fluentsNotInInitState = new HashSet<Integer>();
            for (int i = 0; i < problem.getFluents().size(); i++) {
                fluentsNotInInitState.add(i);
            }

            Term boolTrue = solver.mkBoolean(true);

            for (int p = initPredicatePos.nextSetBit(0); p >= 0; p = initPredicatePos.nextSetBit(p + 1)) {
                Fluent f = problem.getFluents().get(p);
                String symbol = groundToTS(lift_to_time_t(prettyDisplayFluent(f, problem)), 0);
                for (Term t: this.vectorTerms) {
                    if (t.getSymbol().equals(symbol)) {
                        Term constraint = solver.mkTerm(Kind.EQUAL, t, boolTrue);
                        solver.assertFormula(constraint);
                        break;
                    }
                }
                fluentsNotInInitState.remove(p);
                initPredicatePos.set(p);
            }

            for (Integer predicateNotInInitState : fluentsNotInInitState) {
                Fluent f = problem.getFluents().get(predicateNotInInitState);
                String symbol = groundToTS(lift_to_time_t(prettyDisplayFluent(f, problem)), 0);
                for (Term t: this.vectorTerms) {
                    if (t.getSymbol().equals(symbol)) {
                        Term constraint = solver.mkTerm(Kind.EQUAL, t, solver.mkBoolean(false));
                        solver.assertFormula(constraint);
                        break;
                    }
                }
            }



            Boolean modelIsFound = false;
        int sizePlanToSearchFor = 1;
        int safe_check = 0;
        while (!modelIsFound && safe_check < 50) {

            System.out.println("Encode plan of size " + sizePlanToSearchFor);

            // if (sizePlanToSearchFor > 1) {
            //     writer.close();
            //     // Remove the last 4 lines of the file. Which contains a comment, the goal state
            //     // (which will change),
            //     // and the lines check-sat get-model and exit
            //     RandomAccessFile f = new RandomAccessFile("test.SMT", "rw");
            //     int remaining_line_to_delete = 5;
            //     long length = f.length() - 1;
            //     byte b;
            //     while (remaining_line_to_delete > 0) {
            //         do {
            //             length -= 1;
            //             f.seek(length);
            //             b = f.readByte();
            //         } while (b != '\n');
            //         remaining_line_to_delete -= 1;
            //     }
            //     f.setLength(length + 1);
            //     f.close();

            //     writer = new BufferedWriter(new FileWriter("test.SMT", true));
            // }

            // int currentTimeStep = sizePlanToSearchFor - 1;
            // int nextTimeStep = sizePlanToSearchFor;

            // // Declare constants for time step 1
            // declareConstantsForTSCVC5(nextTimeStep, solver);

            // // Write actions_t_implies_precondition_t
            // writer.write("; action_t implies precond_t for ts " + Integer.toString(currentTimeStep) + "\n");
            // for (String act_implies_preconf : this.lifted_actions_t_implies_precondition_t) {
                
            //     writer.write("(assert (" + groundToTS(act_implies_preconf, currentTimeStep) + "))\n");
            // }

            // // Write actions_t_implies_effects_t_plus_1
            // writer.write("; actions_t_implies_effects_t_plus_1 for ts " + Integer.toString(currentTimeStep) + "\n");
            // for (String act_implies_effects : this.lifted_actions_t_implies_effects_t_plus_1) {
            //     writer.write("(assert (" + groundToTS(act_implies_effects, currentTimeStep) + "))\n");
            // }

            // // Write the explanatory frame axioms for this timestep
            // writer.write("; explanatory frame axioms for ts " + Integer.toString(currentTimeStep) + "\n");
            // for (String explanatory_frame_axiom : this.lifted_explanatory_frame_axioms) {
            //     writer.write("(assert (" + groundToTS(explanatory_frame_axiom, currentTimeStep) + "))\n");
            // }

            // // Write the at least one action
            // writer.write("; at least one action for ts " + Integer.toString(currentTimeStep) + "\n");
            // writer.write("(assert (" + groundToTS(this.lifted_at_least_one_action, currentTimeStep) + "))\n");

            // // Write the at most one action
            // writer.write("; at most one action for ts " + Integer.toString(currentTimeStep) + "\n");
            // writer.write("(assert (" + groundToTS(this.lifted_at_most_one_action, currentTimeStep) + "))\n");

            // // Now, we need to add retractable goal state + retractable line check-sat +
            // // retractable line exit
            // writer.write("; Goal state for ts " + Integer.toString(nextTimeStep) + "\n");
            // writer.write("(assert (" + groundToTS(this.lifted_goal_state, nextTimeStep) + "))\n");

            // writer.write("(check-sat)\n");
            // writer.write("(get-model)\n");
            // writer.write("(exit)\n");

            // writer.flush();

            // System.out.println("Launch solver on problem encoded");
            // long endEncodeTime = System.currentTimeMillis();
            // this.getStatistics()
            //         .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

            // long beginSolveTime = System.currentTimeMillis();
            // String responseSolver = executeSMTSolverOnFile(filename);
            // long endSolveTime = System.currentTimeMillis();
            // this.getStatistics()
            //         .setTimeToSearch(this.getStatistics().getTimeToSearch() + (endSolveTime - beginSolveTime));
            // if (fileIsSatisfiable(responseSolver)) {
            //     System.out.println("File is satisfiable !");
            //     // Extract plan from response
            //     SequentialPlan plan = extractPlanFromSolver(problem, responseSolver);
            //     return plan;
            // }
            // else {
            //     System.out.println("File is not satisfiable ");
            //     // Check sat here
            //     safe_check++;
            //     sizePlanToSearchFor++;
            //     beginEncodeTime = System.currentTimeMillis();
            // }
        }

            LOGGER.info("stop to debug\n");
        }

        return null;
    }

    /**
     * Search a solution plan to a specific domain using a SMT solver (cvc5).
     *
     * @param problem the problem to solve.
     * @return the plan found or null if no plan was found.
     */
    @Override
    public Plan solve(Problem problem) {

        System.out.println("Solver problem !");

        this.lifted_actions = encode_lifted_actions(problem);
        this.lifted_predicates = encode_lifted_predicates(problem);
        this.lifted_binary_encoding_temp_variables = encode_lifted_binary_encoding_temp_variables(problem); // Use
                                                                                                            // binary
                                                                                                            // encoding
                                                                                                            // to assert
                                                                                                            // at most
                                                                                                            // one
                                                                                                            // action
                                                                                                            // per time
                                                                                                            // step.
                                                                                                            // Which
                                                                                                            // create
                                                                                                            // new
                                                                                                            // variables

        this.lifted_actions_t_implies_precondition_t = encode_lifted_actions_t_implies_preconditions_t(problem);
        this.lifted_actions_t_implies_effects_t_plus_1 = encode_lifted_actions_t_implies_effects_t_plus_1(problem);
        this.lifted_explanatory_frame_axioms = encode_lifted_explanatory_frame_axioms(problem);
        this.lifted_at_least_one_action = encode_lifted_at_least_one_action(problem);
        this.lifted_at_most_one_action = encode_lifted_at_most_one_action(problem);

        this.lifted_goal_state = encode_lifted_goal_state(problem);

        SequentialPlan plan = null;
        try {
            plan = writeSMTFile(problem);
            // plan = encodeToCVC5(problem);

            // Check if plan is correct with VAL
            

        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // Check if plan is correct
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
            final Rantanplan planner = new Rantanplan();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }
}
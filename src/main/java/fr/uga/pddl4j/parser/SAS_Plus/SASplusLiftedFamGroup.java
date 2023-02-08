package fr.uga.pddl4j.parser.SAS_Plus;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;

import org.apache.logging.log4j.core.util.AuthorizationProvider;

import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.NamedTypedList;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.ParsedDomain;
import fr.uga.pddl4j.parser.Parser;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.TypedSymbol;
import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.util.BitSet;
import fr.uga.pddl4j.util.BitVector;


class GroundCandidate {
    public String schemaCandidate;
    public Vector<String> valueFixedVars;
    public BitSet fluentsMask;

    GroundCandidate(String candidateSchema, Vector<String> valueFixedVars, Problem problem) {
        this.schemaCandidate = candidateSchema;
        this.valueFixedVars = new Vector<String>();
        for (String fixedVarValue : valueFixedVars) {
            this.valueFixedVars.add(fixedVarValue);
        }

        this.fluentsMask = new BitSet(problem.getFluents().size());
    }
}

public class SASplusLiftedFamGroup {

    private static Queue<Candidate> invariantCandidateArr;
    public static HashSet<Candidate> candidatesProved;
    private static HashSet<String> candidateAlreadyChecked;
    // A dictionary which map the name of a type to all the parent of this type
    private static Map<String, HashSet<String>> dictTypeToParentTypes;
    // A dictionary which map the name of a type to all the children of this type
    private static Map<String, HashSet<String>> dictTypeToChildTypes;
    // A dictionary which map the name of an object to the type of the object
    private static Map<String, String> dictObjNameToType;
    // A Set which contains the name of all the static predicate (predicates which are not changed by the actions)
    private static HashSet<String> staticPredicates;

    public static List<Collection<Integer>> cliques;

    /**
     * Return a string containing a fluent in easily readable format
     * 
     * @param f       The fluent to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the fluent in easily readable format
     */
    private static String prettyDisplayFluent(Fluent f, Problem problem) {
        StringBuilder fluentToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        fluentToDisplay.append("FLUENT_" + problem.getPredicateSymbols().get(f.getSymbol()));

        // Then, for each argument of this fluent, add the argument into the string
        for (int fluentArg : f.getArguments()) {
            fluentToDisplay.append("_" + problem.getConstantSymbols().get(fluentArg));
        }

        return fluentToDisplay.toString();
    }

    private static String prettyDisplayLiftedAction(ParsedAction a, Problem problem) {
        StringBuilder liftedActionToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        liftedActionToDisplay.append("ACTION_" + a.getName().getValue());

        // Then, for each argument of this fluent, add the argument into the string
        for (TypedSymbol<String> actionLiftedArg : a.getParameters()) {
            liftedActionToDisplay.append("_" + actionLiftedArg.getValue());
        }

        return liftedActionToDisplay.toString();
    }

    public static void addNewCandidate(Candidate candidate) {

        System.out.println("Add new candidate: \n" + candidate.getUniqueStringRepresentation());

        // We should check if this candidate has not already been added here !
        // So we must have a set of all the candidate that have been seen
        // To do that, we cannot compare candidate directly as it is a too
        // big object (we are not sure)
        String stringRepresentationCandidate = candidate.getUniqueStringRepresentation();
        if (!candidateAlreadyChecked.contains(stringRepresentationCandidate)) {
            invariantCandidateArr.add(candidate);
            candidateAlreadyChecked.add(stringRepresentationCandidate);
        } else {
            System.out.println("Candidate has already been added");
        }

    }

    public static void determinateLiftedFamGroups(Problem problem) {

        // Define some variable
        int maxCandidates = 10_000; // Maximum of generated candidates. Default: 10000
        int maxGroups = 10_000; // Maximum of proved lifted mutex groups. Default: 10000

        System.out.println("Inference of lifted fam-groups...");
        candidateAlreadyChecked = new HashSet<String>();
        candidatesProved = new HashSet<Candidate>();
        preprocessingComputeAllParentsAndChildrenEachTypes(problem);
        preprocessingComputeDictObjectNameToType(problem);
        staticPredicates = preprocessingComputeStaticPredicates(problem);

        invariantCandidateArr = initialCandicatesAllVarsCounted(problem);


        System.out.println("Number initial candidates: " + invariantCandidateArr.size());
        for (Candidate candidate : invariantCandidateArr) {
            System.out.println(candidate.getUniqueStringRepresentation());
        }
        System.out.println("------------------");

        int testedCandidates = 0;

        // TODO change the condition
        while (invariantCandidateArr.size() > 0) {
            // Get an invariant candidate
            Integer numCandidates = invariantCandidateArr.size();
            Candidate candidate = invariantCandidateArr.remove();
            System.out.println("Refinement num " + testedCandidates + " Num cand: " + numCandidates
                    + " -> Pop the candidate: \n" + candidate.getUniqueStringRepresentation());
            // System.out.println(candidate.getUniqueStringRepresentation());
            // Check if the candidate it too heavy for the initialization
            // (there are multiple atom in the initialization which are in the candidate)
            System.out.println("Test checkTooHeavyInit");
            if (checkWeightInitEquals1(candidate, problem)) {
                System.out.println("Test isAnyActionTooHeavy");
                if (!isAnyActionTooHeavy(candidate, problem)) {
                    System.out.println("Test isAnyActionUnbalanced");
                    if (!isAnyActionUnbalanced(candidate, problem)) {
                        System.out.println("***************** Candidate is proved ! ***********************");
                        // Make a full copy of this candidate and add it to the candidates proven
                        Candidate candidateProved = new Candidate(candidate);
                        candidatesProved.add(candidateProved);

                        refineProved(candidate, problem);
                    }
                }
            }
            testedCandidates++;
            System.out.println("-----------------");
        }

        // Remove all sub proved candidates (candidates whoses lifted mutexed as a sub
        // ensemble of another candidate)

        removeSubProvedCandidates();

        // Display all the proved candidates
        System.out.println("Number of lifted fam mutex: " + candidatesProved.size());
        for (Candidate candidateProved : candidatesProved) {
            System.out.println(candidateProved.getUniqueStringRepresentation());
        }
        System.out.println("-----------------");

        // Now, we can ground our mutexes. But there can be overlap between our mutex (2
        // mutex can encode the same variable...)
        // To prevent that, we use the algorithm proposed by helmert in the paper
        // Concise finite-domain representations
        // for PDDL planning tasks ⋆ (see figure 17)

        // TODO: the grounding is way too slow. Improve it...
        Vector<GroundCandidate> allGroundCandidates = groundMutexes(problem, candidatesProved);

        cliques = new ArrayList<>();

        // Return the clique in the correct format
        for (GroundCandidate g : allGroundCandidates) {
            List<Integer> fluentsTakenByGroundCandidate = new ArrayList<>();
            BitSet p = g.fluentsMask;
            for (int fluentId = p.nextSetBit(0); fluentId >= 0; fluentId = p.nextSetBit(fluentId + 1)) {
                fluentsTakenByGroundCandidate.add(fluentId);
                p.set(fluentId);
            }
            cliques.add(fluentsTakenByGroundCandidate);
        }
    }

    /**
     * 
     * Unifies a fluent with an AtomCandidate by iterating over all the arguments of
     * the fluent and comparing them to the parameters of the AtomCandidate.
     * 
     * @param fluentIndex   the index of the fluent in the fluents list of the
     *                      problem
     * @param atomCandidate the AtomCandidate to unify with the fluent
     * @param problem       the problem containing the fluents and relevant
     *                      information for unification
     * 
     * @return true if the fluent and AtomCandidate can be unified, false otherwise
     */
    private static boolean unifyGroundFact(int fluentIdx, AtomCandidate atomCandidate, Problem problem) {
        Fluent fluentToUnifyWith = problem.getFluents().get(fluentIdx);

        boolean failedToUnify = false;

        // Keep a copy of the state of all the variables of the atom candidate
        // In case we failed to unify the fact with this atom candidate,
        // we should reset the values of the variables of the atom candidate to its
        // original state
        Vector<AtomVariable> variablesBackup = new Vector<AtomVariable>();
        for (int i = 0; i < atomCandidate.candidateParent.variables.size(); i++) {
            variablesBackup.add(new AtomVariable(atomCandidate.candidateParent.variables.get(i)));
        }

        // Iterate over all the argument of this fluent
        for (int argId = 0; argId < fluentToUnifyWith.getArguments().length; argId++) {

            // Get the value of the argument (e.g: "block_A" for the first argument of the
            // predicate on block_A block_B for blocksworld)
            String nameArgValue = problem.getConstantSymbols().get(fluentToUnifyWith.getArguments()[argId]);

            // Get the name of the type of the argument (e.g "block" for a block in
            // blocksworld)
            String nameArgType = null;
            // Now, find the type of this object
            for (TypedSymbol<String> typeObj : problem.getParsedProblem().getConstants()) {
                if (typeObj.getValue().equals(nameArgValue)) {
                    nameArgType = typeObj.getTypes().get(0).getValue();
                }
            }

            // Get the parameter of the atom candidate which try to unify with this fluent
            AtomVariable atomParam = atomCandidate.candidateParent.variables.get(atomCandidate.paramsId.get(argId));

            // If it is a counted variable, it can takes all values of a certain type, so
            // just check if the type of the value
            // that it takes correspond to the same type as the type of the argument of the
            // predicate
            if (atomParam.isCountedVar) {

                if (atomParam.typeName == null) {
                    // Set the type of this parameter to the same type of the argument of the
                    // predicate
                    atomParam.typeName = nameArgType;
                    continue;
                } else if (pddlTypeIsParent(nameArgType, atomParam.typeName, problem)) {
                    // Do nothing here... I think ? Or we should restrict the type of value taken
                    // by the action to the type of atomParam surely... TODO !!
                } else if (!atomParam.typeName.equals(nameArgType)
                        && !pddlTypeIsParent(atomParam.typeName, nameArgType, problem)) {
                    // This counted variable is already bound to another type !
                    // Hence, we cannot unify this predicate with this atomCandidate !
                    failedToUnify = true;
                    break;
                }
            } else {
                // Check if this atom parameters is already bound to the same type as the action
                // parameter
                if (atomParam.typeName != null) {

                    if (pddlTypeIsParent(nameArgType, atomParam.typeName, problem)) {
                        // Same as above. I don't know there...
                    } else if (!atomParam.typeName.equals(nameArgType)
                            && !pddlTypeIsParent(atomParam.typeName, nameArgType, problem)) {
                        // This atom parameter if already bound to another type !
                        failedToUnify = true;
                        break;
                    }

                    // Now check if this atom parameter is bound to a variable
                    if (atomParam.value != null) {
                        // Now, Check if the value taken by this atom parameter is the same than the
                        // value taken by the argument of the predicate
                        if (!atomParam.value.equals(nameArgValue)) {
                            // This fixed variable is already fixed to another object !
                            failedToUnify = true;
                            break;
                        }
                    } else {
                        // Set the value of this atom parameter to the value of the parameter
                        atomParam.value = nameArgValue;
                    }

                    // Everything is OK if we are here
                } else {
                    // Set the type and the value of this atom parameter to the value of the
                    // parameter
                    atomParam.typeName = nameArgType;
                    atomParam.value = nameArgValue;
                }
            }
        }

        if (failedToUnify) {
            // We should reset all the value than we have changed to their original
            // values...
            atomCandidate.candidateParent.variables.clear();
            atomCandidate.candidateParent.variables = variablesBackup;
            // Return false since we failed to unify
            return false;
        }
        return true;
    }

    /**
     * 
     * Unifies a lifted fluent with an AtomCandidate by iterating over all the
     * arguments of
     * the lifted fluent and comparing them to the parameters of the AtomCandidate.
     * 
     * @param liftedAction                 the lifted action which contains the
     *                                     lifted fact
     * @param liftedFact                   the lifted fluent
     * @param atomCandidate                the AtomCandidate to unify with the
     *                                     fluent
     * @param problem                      the problem containing the fluents and
     *                                     relevant
     *                                     information for unification
     * @param fixedVariableUndefinedFailed If a fixed variable of the atom candidate
     *                                     is undefined, failed to unify the lifted
     *                                     fact
     * 
     * @return true if the fluent and AtomCandidate can be unified, false otherwise
     */
    private static boolean unifyLiftedFact(ParsedAction liftedAction, Expression<String> liftedFact,
            AtomCandidate atomCandidate, Problem problem, boolean fixedVariableUndefinedFailed) {

        boolean failedToUnify = false;

        // Keep a copy of the state of all the variables of the atom candidate
        // In case we failed to unify the fact with this atom candidate,
        // we should reset the values of the variables of the atom candidate to its
        // original state
        Vector<AtomVariable> variablesBackup = new Vector<AtomVariable>();
        for (int i = 0; i < atomCandidate.candidateParent.variables.size(); i++) {
            variablesBackup.add(new AtomVariable(atomCandidate.candidateParent.variables.get(i)));
        }

        // Iterate over all the argument of this lifted fluent
        for (int argId = 0; argId < liftedFact.getArguments().size(); argId++) {

            // Get the lifted value of the argument
            String nameArgValue = liftedFact.getArguments().get(argId).getValue();

            // Get the name of the type of the argument (e.g "block" for a block in
            // blocksworld)
            String nameArgType = null;
            for (TypedSymbol<String> param : liftedAction.getParameters()) {
                if (param.getValue().equals(nameArgValue)) {
                    nameArgType = param.getTypes().get(0).getValue();
                    break;
                }
            }

            // Get the parameter of the atom candidate which try to unify with this fluent
            AtomVariable atomParam = atomCandidate.candidateParent.variables.get(atomCandidate.paramsId.get(argId));

            // If it is a counted variable, it can takes all values of a certain type, so
            // just check if the type of the value
            // that it takes correspond to the same type as the type of the argument of the
            // predicate
            if (atomParam.isCountedVar) {

                if (atomParam.typeName == null) {
                    // Set the type of this parameter to the same type of the argument of the
                    // predicate
                    atomParam.typeName = nameArgType;
                    continue;
                } else if (pddlTypeIsParent(nameArgType, atomParam.typeName, problem)) {
                    // Do nothing here... I think ? Or we should restrict the type of value taken
                    // by the action to the type of atomParam surely... TODO !!

                    // If the type of the argument is a parent of the type
                    // of the atomVar, then we cannot be sure that we can unify
                    if (fixedVariableUndefinedFailed) {
                        failedToUnify = true;
                        break;
                    }
                } else if (!atomParam.typeName.equals(nameArgType)
                        && !pddlTypeIsParent(atomParam.typeName, nameArgType, problem)) {
                    // This counted variable is already bound to another type !
                    // Hence, we cannot unify this predicate with this atomCandidate !
                    failedToUnify = true;
                    break;
                }
            } else {
                // Check if this atom parameters is already bound to the same type as the action
                // parameter
                if (atomParam.typeName != null) {

                    if (pddlTypeIsParent(nameArgType, atomParam.typeName, problem)) {
                        // Same as above. I don't know there...
                    } else if (!atomParam.typeName.equals(nameArgType)
                            && !pddlTypeIsParent(atomParam.typeName, nameArgType, problem)) {
                        // This atom parameter if already bound to another type !
                        failedToUnify = true;
                        break;
                    }

                    // Now check if this atom parameter is bound to a variable
                    if (atomParam.value != null) {
                        // Now, Check if the value taken by this atom parameter is the same than the
                        // value taken by the argument of the predicate
                        if (!atomParam.value.equals(nameArgValue)) {
                            // This fixed variable is already fixed to another object !
                            failedToUnify = true;
                            break;
                        }
                    } else {
                        if (fixedVariableUndefinedFailed) {
                            failedToUnify = true;
                            break;
                        }
                        // Set the value of this atom parameter to the value of the parameter
                        atomParam.value = nameArgValue;
                    }

                    // Everything is OK if we are here
                } else {

                    if (fixedVariableUndefinedFailed) {
                        failedToUnify = true;
                        break;
                    }
                    // Set the type and the value of this atom parameter to the value of the
                    // parameter
                    atomParam.typeName = nameArgType;
                    atomParam.value = nameArgValue;
                }
            }
        }

        if (failedToUnify) {
            // We should reset all the value than we have changed to their original
            // values...
            atomCandidate.candidateParent.variables.clear();
            atomCandidate.candidateParent.variables = variablesBackup;
            // Return false since we failed to unify
            return false;
        }
        return true;
    }

    /**
     * Refine candidate cand by changing types of candidate variables so that
     * atom and cand_atom cannot be unified.
     * 
     * @param atomCandidate
     * @param predWhichCanUnifyWithCand1
     */
    private static void refineVariableType(Candidate candidate, AtomCandidate atomCandidate,
            int predWhichCanUnifyWithCand,
            Problem problem) {

        Fluent f = problem.getFluents().get(predWhichCanUnifyWithCand);
        // Iterate over all arguments of the predicate
        for (int argId = 0; argId < atomCandidate.paramsId.size(); argId++) {

            // System.out.println("Arg: " + argId);

            // Get the name of the type of the parameter of the atom candidate
            String typeNameArgAtomCandidate = atomCandidate.candidateParent.variables
                    .get(atomCandidate.paramsId.get(argId)).typeName;

            // Get the name of the obj of the parameter of the predicate which can unify
            // with the atom candidate
            String nameObj = problem.getConstantSymbols().get(f.getArguments()[argId]);
            String typeNameArgPredicate = null;
            // Now, find the type of this object
            for (TypedSymbol<String> typeObj : problem.getParsedProblem().getConstants()) {
                if (typeObj.getValue().equals(nameObj)) {
                    typeNameArgPredicate = typeObj.getTypes().get(0).getValue();
                }
            }

            // Now, we must check that the type of the argument of the predicate is a
            // subtype of the type of the argument of the atomCandidate
            if (pddlTypeIsParent(typeNameArgAtomCandidate, typeNameArgPredicate, problem)) {

                // Now, to prevent the unification, we must take all the type children of our
                // atom Candidate arg
                // which are not among the type parent and the type children of the predicate
                // arg
                HashSet<String> typesWhichPreventUnify = new HashSet<String>(
                        dictTypeToChildTypes.get(typeNameArgAtomCandidate));
                typesWhichPreventUnify.removeAll(dictTypeToParentTypes.get(typeNameArgPredicate));
                typesWhichPreventUnify.removeAll(dictTypeToChildTypes.get(typeNameArgPredicate));
                typesWhichPreventUnify.remove(typeNameArgPredicate);

                // To create less candidates, get only the parents of all these types
                Iterator<String> iterator = typesWhichPreventUnify.iterator();
                while (iterator.hasNext()) {
                    String type = iterator.next();
                    typesWhichPreventUnify.removeAll(dictTypeToChildTypes.get(type));
                }

                // Now, for each type available, create a new candidate
                for (String newTypeName : typesWhichPreventUnify) {

                    // Create our new candidate
                    Candidate newCandidate = new Candidate(candidate);
                    newCandidate.variables.get(atomCandidate.paramsId.get(argId)).typeName = newTypeName;
                    addNewCandidate(newCandidate);
                }
            }
        }
    }

    /**
     * Refine candidate cand by changing types of candidate variables so that
     * atom and cand_atom cannot be unified.
     * 
     * @param atomCandidate
     * @param predWhichCanUnifyWithCand1
     */
    private static void refineVariableTypeLifted(Candidate candidate, AtomCandidate atomCandidate,
            ParsedAction liftedAction, Expression<String> liftedPred,
            Problem problem) {

        // Iterate over all arguments of the lifted predicate
        for (int argId = 0; argId < liftedPred.getArguments().size(); argId++) {

            // System.out.println("Arg: " + argId);

            // Get the name of the type of the parameter of the atom candidate
            String typeNameArgAtomCandidate = atomCandidate.candidateParent.variables
                    .get(atomCandidate.paramsId.get(argId)).typeName;

            // Get name of the type of this argument
            // To do that, we need the name of the parameter first
            String nameParameter = liftedPred.getArguments().get(argId).getValue();
            String typeNameArgPredicate = null;
            // And then, we need to find the type associated with this parameters
            for (TypedSymbol<String> param : liftedAction.getParameters()) {
                if (param.getValue().equals(nameParameter)) {
                    typeNameArgPredicate = param.getTypes().get(0).getValue();
                }
            }

            // Now, we must check that the type of the argument of the predicate is a
            // subtype of the type of the argument of the atomCandidate
            if (pddlTypeIsParent(typeNameArgAtomCandidate, typeNameArgPredicate, problem)) {

                // Now, to prevent the unification, we must take all the type children of our
                // atom Candidate arg
                // which are not among the type parent and the type children of the predicate
                // arg
                HashSet<String> typesWhichPreventUnify = new HashSet<String>(
                        dictTypeToChildTypes.get(typeNameArgAtomCandidate));
                typesWhichPreventUnify.removeAll(dictTypeToParentTypes.get(typeNameArgPredicate));
                typesWhichPreventUnify.removeAll(dictTypeToChildTypes.get(typeNameArgPredicate));
                typesWhichPreventUnify.remove(typeNameArgPredicate);

                // To create less candidates, get only the parents of all these types
                Iterator<String> iterator = typesWhichPreventUnify.iterator();
                while (iterator.hasNext()) {
                    String type = iterator.next();
                    typesWhichPreventUnify.removeAll(dictTypeToChildTypes.get(type));
                }

                // Now, for each type available, create a new candidate
                for (String newTypeName : typesWhichPreventUnify) {

                    // Create our new candidate
                    Candidate newCandidate = new Candidate(candidate);
                    newCandidate.variables.get(atomCandidate.paramsId.get(argId)).typeName = newTypeName;
                    addNewCandidate(newCandidate);
                }
            }
        }
    }

    private static void refineTooHeavyAction() {
        System.out.println("Refine too heavy action\n");
        // TODO implement this function
    }

    /**
     * Refine candidate cand by extending it with more atoms so that add
     * effects are balanced.
     */
    private static void refineExtend(Candidate candidate, Problem problem, ParsedAction liftedAction) {

        int numberEffActions = liftedAction.getEffects().getChildren().size();
        if (numberEffActions == 0 && liftedAction.getEffects().getSymbol() != null) {
            numberEffActions = 1;
        }

        if (numberEffActions <= 1) {
            return;
        }

        // Iterate over all negative effect of the action
        for (int negEffId = 0; negEffId < liftedAction.getEffects().getChildren().size(); negEffId++) {

            // If it is not a negative effect, pass this effect
            if (!liftedAction.getEffects().getChildren().get(negEffId).getConnector().getImage()
                    .equals("not")) {
                continue;
            }

            Expression<String> negEff = liftedAction.getEffects().getChildren().get(negEffId).getChildren()
                    .get(0);

            // Get the name of the negative predicate
            String negEffPredName = negEff.getSymbol().getValue();

            // The predicate name should not already be in the AtomCandidates of the
            // candidate
            if (candidate.hasPredicateInMutexGroup(negEffPredName)) {
                continue;
            }

            // Now, we should look at all the ways for extending our candidate with a new
            // atomCandidate
            // so that this predicate can be unified with the candidate

            // An eady way to add an atom candidate, is just to set all his variables to a
            // counted variable
            // we are sure in this way that this predicate can be unified with the atom
            // Candidate

            // The second point is the following: if we set each variable of this predicate
            // to a fixed variable
            // which other variable of the atom candidate are bound to the same variable
            // (this correspond
            // to the atomCandidate which are also in the positive effect/precondition of
            // the action) ?
            // If this bound variable are counted variable, set it to counted variable and
            // give the same value that
            // for the new argument in the candidate

            // Now, iterate over all positive effect of the action and see if this
            // positive effect is in the candidate's AtomCandidate (should get at least one)
            for (int posEffId = 0; posEffId < liftedAction.getEffects().getChildren().size(); posEffId++) {

                Expression<String> posEff = liftedAction.getEffects().getChildren().get(posEffId);

                // If it is a negative effect, pass this effect
                if (posEff.getConnector().getImage().equals("not")) {
                    continue;
                }

                // Get the name of the predicate of the positive effect of the action
                String posEffPredName = posEff.getSymbol().getValue();

                // Iterate over all atomCandidate to get the candidate atom which contains this
                // positive action
                for (Integer idxAtomCandidate = 0; idxAtomCandidate < candidate.mutexGroup.size(); idxAtomCandidate++) {

                    AtomCandidate atomCandidate = candidate.mutexGroup.get(idxAtomCandidate);
                    // Check if the candidate contains this atom
                    if (!atomCandidate.predSymbolName.equals(posEffPredName)) {
                        continue;
                    }

                    System.out.println("Negative effect: " + negEffPredName);
                    System.out.println("Positive effect: " + posEffPredName);

                    // It is. now, we must iterate over all arguments of this positive predicate
                    // effect and see if the value
                    // is bound to a negative effect parameter. If that's the case, we change in our
                    // candidate
                    // the counted variable to take a fixed variable which will be the same at the
                    // new AtomCandidate
                    // corresponding parameter. If it is already a fix variable, the new candidate
                    // will have to take the same
                    // fixed variable.
                    recursiveFindAndAddAllNewPotentielCandidateRefineExtend(problem, candidate, liftedAction, negEff, 0,
                            posEff,
                            idxAtomCandidate, new Vector<Integer>());
                }
            }
        }
    }

    // TODO implement the function
    public static void refineProved(Candidate candidate, Problem problem) {

        // Iterate over all lifted function
        for (ParsedAction liftedAction : problem.getParsedProblem().getActions()) {
            System.out.println(prettyDisplayLiftedAction(liftedAction, problem));

            int numberEffActions = liftedAction.getEffects().getChildren().size();
            if (numberEffActions == 0 && liftedAction.getEffects().getSymbol() != null) {
                numberEffActions = 1;
            }

            if (numberEffActions <= 1) {
                continue;
            }
            // Now, iterate over all negative predicate of this action
            // Iterate over all negative effects of the parsedAction
            for (int negEffId = 0; negEffId < liftedAction.getEffects().getChildren().size(); negEffId++) {

                // If it is not a negative effect, pass this effect
                if (!liftedAction.getEffects().getChildren().get(negEffId).getConnector().getImage()
                        .equals("not")) {
                    continue;
                }

                Expression<String> negEff = liftedAction.getEffects().getChildren().get(negEffId).getChildren()
                        .get(0);

                // Get the name of the negative predicate
                String negEffPredName = negEff.getSymbol().getValue();

                // Check if this delete effect can be unified with the candidate
                // Check if this positive effect can be unified by an atom candidate
                for (AtomCandidate atomCandidate : candidate.mutexGroup) {

                    if (!atomCandidate.predSymbolName.equals(negEffPredName)) {
                        continue;
                    }

                    System.out.println("Del effect " + negEffPredName);

                    // Here, we should clear all the candidate variables values of arguments
                    for (AtomVariable var : candidate.variables) {
                        var.value = null;
                    }

                    // Now, we must ground the args of the atomCandidate to a specific value to
                    // unify with the negative effect of the action
                    if (!unifyLiftedFact(liftedAction, negEff, atomCandidate, problem, false)) {
                        continue;
                    }

                    // Now check if an add effect can also be unified with
                    // To see if we can improve this candidate, we must now iterate over all the
                    // add effects of the action and see
                    // if we can unify a add effect of the action with one of the atom candidate

                    // Create a variable which will check if this action negative effect predicate
                    // is balanced with a positive effect predicate of the action
                    boolean negEffIsBalanced = false;
                    // Iterate over all positive effects of the parsedAction
                    for (int posEffId = 0; posEffId < liftedAction.getEffects().getChildren().size(); posEffId++) {

                        Expression<String> posEff = liftedAction.getEffects().getChildren().get(posEffId);

                        // If it is a negative effect, pass this effect
                        if (posEff.getConnector().getImage().equals("not")) {
                            continue;
                        }

                        // Get the name of the predicate of the positive effect of the action
                        String posEffPredName = posEff.getSymbol().getValue();

                        // Check if this positive effect can be unified by an atom candidate (e.g: the
                        // negative effect if balanced)
                        for (AtomCandidate atomCandidate2 : candidate.mutexGroup) {

                            if (!atomCandidate2.predSymbolName.equals(posEffPredName)) {
                                continue;
                            }
                            System.out.println("pos effect " + posEffPredName);
                            // Now we can check if we can ground the atom condidate to the value of the
                            // predicate

                            if (unifyLiftedFact(liftedAction, posEff, atomCandidate2, problem, true)) {

                                // TODO
                                // we also must check that there is a precondition exactly matching the delete
                                // effect so we can be sure that the delete effect is present in the state the
                                // action is applied on, i.e., that the delete effect really balances the add
                                // effect.

                                // If we have succeeded to unify, continue to the next positive effect of the
                                // action (since we already know that this positive effect is balanced)
                                negEffIsBalanced = true;
                                break;
                            }

                            if (negEffIsBalanced) {
                                break;
                            }
                        }
                    }

                    // If the negative predicate is not balanced, add all positive predicate
                    // possible to extend the candidate
                    if (!negEffIsBalanced) {
                        // We can refine by extending our candidate
                        System.out.println("We can refine the proved candidate !\n");
                        // Extend our candidate with all positive effects
                        for (int posEffId = 0; posEffId < liftedAction.getEffects().getChildren().size(); posEffId++) {

                            Expression<String> posEff = liftedAction.getEffects().getChildren().get(posEffId);

                            // If it is a negative effect, pass this effect
                            if (posEff.getConnector().getImage().equals("not")) {
                                continue;
                            }

                            // Check if our atom candidate does not already possess this predicate
                            if (candidate.hasPredicateInMutexGroup(posEff.getSymbol().getValue())) {
                                continue;
                            }

                            // Get the name of the predicate of the positive effect of the action
                            String posEffPredName = posEff.getSymbol().getValue();

                            recursiveFindAndAddAllNewPotentielCandidateRefineExtend(problem, candidate, liftedAction,
                                    posEff, 0, negEff, candidate.mutexGroup.indexOf(atomCandidate),
                                    new Vector<Integer>());
                        }
                    }
                }
            }
        }

        // Some cleaning at the end
        for (AtomVariable var : candidate.variables) {
            var.value = null;
        }
    }

    private static void recursiveFindAndAddAllNewPotentielCandidateRefineExtend(Problem problem, Candidate candidate,
            ParsedAction liftedAction,
            Expression<String> predToAdd, Integer currentArgIdOfPredToAdd,
            Expression<String> predWhichIsUnified,
            Integer idxatomCandidateCorrespondingTopredUnified,
            Vector<Integer> pointerToBoundVariableOfAtomCandidate) {

        // We stop from iterating if currentArgIdOfNegEff > arity of the negEff
        if (currentArgIdOfPredToAdd == predToAdd.getArguments().size()) {
            // Now, we have all the information to extend our candidate, but let's do it
            // in a separate function

            addNewCandidateFromRefineExtend(problem, candidate, liftedAction, predToAdd,
                    idxatomCandidateCorrespondingTopredUnified,
                    pointerToBoundVariableOfAtomCandidate);
            return;
        }

        // Get the value of the current argument for the negative effect of the action
        String valNegEffPredCurrentArg = predToAdd.getArguments().get(currentArgIdOfPredToAdd).getValue();

        // See if the positive effect is bound to this argument
        for (int predUnifiedArgId = 0; predUnifiedArgId < predWhichIsUnified.getArguments()
                .size(); predUnifiedArgId++) {
            if (predWhichIsUnified.getArguments().get(predUnifiedArgId).getValue().equals(valNegEffPredCurrentArg)) {
                // It means that if the new Atom corresponding to the negative effect take a
                // fixed variable,
                // it must be the same as this argument of the atomCandidate which represent the
                // positive effect

                // Make a copy of the pointer since we want different Vector for the different
                // new candidate possible
                Vector<Integer> newPointerToBoundVariableOfAtomCandidate = new Vector<Integer>();
                for (Integer p : pointerToBoundVariableOfAtomCandidate) {
                    newPointerToBoundVariableOfAtomCandidate.add(p);
                }

                // Say that we must point to this value in the AtomCandidate which represent the
                // positive effect
                newPointerToBoundVariableOfAtomCandidate.add(predUnifiedArgId);

                recursiveFindAndAddAllNewPotentielCandidateRefineExtend(problem, candidate, liftedAction, predToAdd,
                        currentArgIdOfPredToAdd + 1,
                        predWhichIsUnified, idxatomCandidateCorrespondingTopredUnified,
                        newPointerToBoundVariableOfAtomCandidate);
            }
        }

        // By default, let's add a counted variable for this argument
        // Make a copy of the pointer since we want different Vector for the different
        // new candidate possible
        Vector<Integer> newPointerToBoundVariableOfAtomCandidate = new Vector<Integer>();
        for (Integer p : pointerToBoundVariableOfAtomCandidate) {
            newPointerToBoundVariableOfAtomCandidate.add(p);
        }
        // We use the -1 to indicate to use a counted variable instead of a fixed
        // variable bound to a value of the positive effect
        newPointerToBoundVariableOfAtomCandidate.add(-1);
        recursiveFindAndAddAllNewPotentielCandidateRefineExtend(problem, candidate, liftedAction, predToAdd,
                currentArgIdOfPredToAdd + 1, predWhichIsUnified,
                idxatomCandidateCorrespondingTopredUnified, newPointerToBoundVariableOfAtomCandidate);
    }

    private static void addNewCandidateFromRefineExtend(Problem problem, Candidate candidate,
            ParsedAction liftedAction,
            Expression<String> negEff,
            Integer idxatomCandidateCorrespondingToPosAction,
            Vector<Integer> pointerToBoundVariableOfAtomCandidate) {

        // Create a new candidate
        Candidate newCandidate = new Candidate(candidate);

        // Get the atomCandidate which can unify with the positive action
        AtomCandidate atomCandidateWhichCanUnifyWithThePosAction = newCandidate.mutexGroup
                .get(idxatomCandidateCorrespondingToPosAction);

        AtomCandidate newAtomCandidate = new AtomCandidate(atomCandidateWhichCanUnifyWithThePosAction.candidateParent,
                negEff.getSymbol().getValue());
        newCandidate.mutexGroup.add(newAtomCandidate);

        for (Integer argNegEffId = 0; argNegEffId < pointerToBoundVariableOfAtomCandidate.size(); argNegEffId++) {

            Integer idParamBind = pointerToBoundVariableOfAtomCandidate.get(argNegEffId);

            // If this parameter must be a fixed variable
            if (idParamBind >= 0) {
                // Check the value of the AtomCandidate for this variable.
                // If it is a fixed variable, the new AtomCandidate should point
                // to the same variable
                // If it is a counted variable, set it to a fixed variable, and then, the
                // new AtomCandidate should point to this variable
                AtomVariable varBind = atomCandidateWhichCanUnifyWithThePosAction.candidateParent.variables
                        .get(atomCandidateWhichCanUnifyWithThePosAction.paramsId.get(idParamBind));
                if (varBind.isCountedVar) {
                    // Set the variable to fixed var
                    varBind.isCountedVar = false;
                }

                // We also may need to change the type of the parameter. If the action param
                // is a subset of our atom Candidate param
                // To do that, we need the name of the parameter first
                String nameParameter = negEff.getArguments().get(argNegEffId).getValue();
                String nameTypeParameter = null;
                // And then, we need to find the type associated with this parameters
                for (TypedSymbol<String> param : liftedAction.getParameters()) {
                    if (param.getValue().equals(nameParameter)) {
                        nameTypeParameter = param.getTypes().get(0).getValue();
                    }
                }

                if (dictTypeToChildTypes
                        .get(newCandidate.variables.get(atomCandidateWhichCanUnifyWithThePosAction.paramsId
                                .get(idParamBind)).typeName)
                        .contains(nameTypeParameter)) {
                    newCandidate.variables.get(atomCandidateWhichCanUnifyWithThePosAction.paramsId
                            .get(idParamBind)).typeName = nameTypeParameter;
                }

                // Make the new atomCandidate pointe to the same atomVariable for this argument
                newAtomCandidate.paramsId.add(atomCandidateWhichCanUnifyWithThePosAction.paramsId.get(idParamBind));
            }
            // If it is a counted variable
            else {
                // Get the type of this argument
                // To do that, we need the name of the parameter first
                // String nameParameter = negEff.getArguments().get(argNegEffId).getValue();
                // String nameTypeParameter = null;
                // // And then, we need to find the type associated with this parameters
                // for (TypedSymbol<String> param : liftedAction.getParameters()) {
                // if (param.getValue().equals(nameParameter)) {
                // nameTypeParameter = param.getTypes().get(0).getValue();
                // }
                // }

                // This type is not necesserely the best one to extend our action.
                // A more general way is to add the more generat type for this predicate
                // (so not the type taken by the arguement of this predication for this action
                // but the type that this argument can take in the more general way.
                String predicateName = negEff.getSymbol().getValue();
                String nameTypeParameter = null;
                // Find the predicat object associated with this problem
                for (NamedTypedList predicate : problem.getParsedProblem().getPredicates()) {
                    if (predicate.getName().getValue().equals(predicateName)) {
                        nameTypeParameter = predicate.getArguments().get(argNegEffId).getTypes().get(0).getValue();
                    }
                }

                // Add a new counted variable for the candidate
                AtomVariable newCountedVariable = new AtomVariable(nameTypeParameter, true);
                newAtomCandidate.candidateParent.variables.add(newCountedVariable);
                // Make the atomCandidate parameters point to the new counted variable
                newAtomCandidate.paramsId.add(newAtomCandidate.candidateParent.variables.size() - 1);
            }
        }

        // We can now add our candidate to our queue of candidate
        addNewCandidate(newCandidate);
    }

    /**
     * Refine candidate by changing counted variables to non-counted
     * variables so that a1 and a2 cannot be unified with cand_atom1 and
     * cand_atom2.
     * 
     * @param atomCandidate
     * @param predWhichCanUnifyWithCand1
     */
    private static void refineCountedVariable(Candidate candidate, AtomCandidate atomCandidate1,
            AtomCandidate atomCandidate2,
            int predWhichCanUnifyWithCand1, int predWhichCanUnifyWithCand2, Problem problem) {

        Fluent f1 = problem.getFluents().get(predWhichCanUnifyWithCand1);
        Fluent f2 = problem.getFluents().get(predWhichCanUnifyWithCand2);

        // Iterate over our candidate atom parameters
        for (int i = 0; i < atomCandidate1.paramsId.size(); i++) {
            AtomVariable param = atomCandidate1.candidateParent.variables.get(atomCandidate1.paramsId.get(i));

            // If predWhichCanUnifyWithCand[1,2] differ in a argument corresonding to
            // counted variable,
            // then we can try to change this variable to non-counted variable
            if (param.isCountedVar) {
                // Check if predWhichCanUnifyWithCand have a different value
                if (f1.getArguments()[i] != f2.getArguments()[i]) {
                    // They do have a different value ! So change the counted variable for a fixed
                    // variable for this argument
                    // And add this new candidate to the vectors of candidates

                    // create a copy of the current candidate
                    Candidate newCandidate = new Candidate();
                    // the newCandidate should get the same variables as the old one
                    for (AtomVariable var : candidate.variables) {
                        newCandidate.variables.add(new AtomVariable(var));
                    }
                    for (AtomCandidate atomCand : candidate.mutexGroup) {
                        AtomCandidate atomCandCopy = new AtomCandidate(atomCand);
                        atomCandCopy.candidateParent = newCandidate;
                        newCandidate.mutexGroup.add(atomCandCopy);
                    }

                    // Set the variable countedVar of the corresponding atomCandidate of the new
                    // Candidate to false
                    newCandidate.variables.get(atomCandidate1.paramsId.get(i)).isCountedVar = false;

                    addNewCandidate(newCandidate);
                }
            }
        }
    }

    private static void refineHeavyInit(Candidate candidate, AtomCandidate atomCandidate1,
            AtomCandidate atomCandidate2,
            int predWhichCanUnifyWithCand1, int predWhichCanUnifyWithCand2, Problem problem) {

        // refine variable type
        refineVariableType(candidate, atomCandidate1, predWhichCanUnifyWithCand1, problem);
        refineVariableType(candidate, atomCandidate2, predWhichCanUnifyWithCand2, problem);

        // refine variable counted if atomCandidate1 == atomCandidate2
        if (atomCandidate1 == atomCandidate2) {
            refineCountedVariable(candidate, atomCandidate1, atomCandidate2, predWhichCanUnifyWithCand1,
                    predWhichCanUnifyWithCand2, problem);
        }

        return;
    }

    private static void refineHeavyAction(Candidate candidate, ParsedAction liftedAction, AtomCandidate atomCandidate1,
            AtomCandidate atomCandidate2,
            Expression<String> predWhichCanUnifyWithCand1, Expression<String> predWhichCanUnifyWithCand2,
            Problem problem) {

        // refine variable type
        refineVariableTypeLifted(candidate, atomCandidate1, liftedAction, predWhichCanUnifyWithCand1, problem);
        refineVariableTypeLifted(candidate, atomCandidate2, liftedAction, predWhichCanUnifyWithCand2, problem);

        // TODO implement refineCountedVariableLifted here !
        // refine variable counted if atomCandidate1 == atomCandidate2
        // if (atomCandidate1 == atomCandidate2) {
        // refineCountedVariable(candidate, atomCandidate1, atomCandidate2,
        // predWhichCanUnifyWithCand1,
        // predWhichCanUnifyWithCand2, problem);
        // }

        return;
    }

    private static boolean fluentIsInCache(Fluent f, HashSet<ArrayList<Integer>> cache) {

        return false;
    }

    private static boolean checkWeightInitEquals1(Candidate candidate, Problem problem) {

        // Iterate over each positive predicate of the initialization state of the
        // problem
        // (we do not care about the negative predicates)
        BitVector initPredicatePos = problem.getInitialState().getPositiveFluents();
        boolean unified = false;
        boolean candidateTooHeavyInit = false;

        // Create a cache to avoid recomputing multiple time the same type of fluent (fluent with the same predicat symbol and same type of objects for arguments)
        HashSet<String> cacheit1 = new HashSet<String>();

        for (int it1 = initPredicatePos.nextSetBit(0); it1 >= 0; it1 = initPredicatePos.nextSetBit(it1 + 1)) {
            Fluent fluentInit = problem.getFluents().get(it1);

            // Check if the fluent is in cache
            StringBuilder cacheFluent = new StringBuilder();
            cacheFluent.append(problem.getPredicateSymbols().get(fluentInit.getSymbol()));
            for (int i = 0; i < fluentInit.getArguments().length; i++) {
                cacheFluent.append("_" + dictObjNameToType.get(problem.getConstantSymbols().get(fluentInit.getArguments()[i])));
            }
            if (cacheit1.contains(cacheFluent.toString())) {
                continue;
            }

            // Add the fluent to the cache to avoid retrying the same fluent later
            cacheit1.add(cacheFluent.toString());

            // System.out.println(prettyDisplayFluent(fluentInit, problem));

            // Check if a param of a candidate will contains this predicate
            for (AtomCandidate atomCandidate1 : candidate.mutexGroup) {
                // First, the param symbol need to be on the same than the init predicate symbol
                if (!atomCandidate1.predSymbolName.equals(problem.getPredicateSymbols().get(fluentInit.getSymbol()))) {
                    continue;
                }

                // Clean the values taken by all variables of the candidate
                for (AtomVariable var : candidate.variables) {
                    // var.typeName = null;
                    var.value = null;
                }

                // Try to ground the candidate atom with the init predicate atom
                if (!unifyGroundFact(it1, atomCandidate1, problem)) {
                    continue;
                }

                unified = true;

                // Now, iterate over the remaining initial states predicate and check if we can
                // unify
                // another fact (if this happenend, it means our candidate is too heavy)

                BitVector initPredicatePos2 = problem.getInitialState().getPositiveFluents();

                // In the same way, create a cache for the 2nd iterator
                HashSet<String> cacheit2 = new HashSet<String>();

                for (int it2 = initPredicatePos2.nextSetBit(it1 + 1); it2 >= 0; it2 = initPredicatePos2
                        .nextSetBit(it2 + 1)) {

                    Fluent fluentInit2 = problem.getFluents().get(it2);

                    // Check if the fluent is in cache
                    StringBuilder cacheFluent2 = new StringBuilder();
                    cacheFluent2.append(problem.getPredicateSymbols().get(fluentInit2.getSymbol()));
                    for (int i = 0; i < fluentInit2.getArguments().length; i++) {
                        cacheFluent2.append("_" + dictObjNameToType.get(problem.getConstantSymbols().get(fluentInit2.getArguments()[i])));
                    }
                    if (cacheit2.contains(cacheFluent2.toString())) {
                        continue;
                    }

                    // Add the fluent to the cache to avoid retrying the same fluent later
                    cacheit2.add(cacheFluent2.toString());

                    for (AtomCandidate atomCandidate2 : candidate.mutexGroup) {

                        if (!atomCandidate2.predSymbolName
                                .equals(problem.getPredicateSymbols().get(fluentInit2.getSymbol()))) {
                            continue;
                        }

                        if (unifyGroundFact(it2, atomCandidate2, problem)) {
                            // That's a problem, we can unify multiple facts with the atoms candidates, it
                            // means that this is not a mutex... (weight too heavy, at least = 2)
                            // Let's make an refinement

                            System.out.println("a1: " + prettyDisplayFluent(fluentInit, problem));
                            System.out.println("a2: " + prettyDisplayFluent(fluentInit2, problem));
                            System.out.println("Candidate is too heavy !");
                            refineHeavyInit(candidate, atomCandidate1, atomCandidate2, it1,
                                    it2, problem);

                            return false;
                            // candidateTooHeavyInit = true;
                        }
                    }
                }
            }
            initPredicatePos.set(it1);
        }

        if (candidateTooHeavyInit) {
            return false;
        }

        // If we have at least one unified (weight >= 1) and we never add two unified in
        // the same time (weight < 2)
        // Then we have a weight = 1. Else 0
        return unified;
    }

    /**
     * 
     * Determines if a lifted action is balanced with a given candidate and problem.
     * (A candidate is balanced in an action, if having a ground atom in action’s
     * positive effect implies having another ground atom in its precondition and
     * negative effect).
     * 
     * @param candidate    The candidate to check against the lifted action
     * @param problem      The problem the lifted action belongs to
     * @param liftedAction The lifted action to check for balance
     * 
     * @return true if the lifted action is balanced with the given candidate, false
     *         otherwise
     */
    private static boolean isActionBalanced(Candidate candidate, Problem problem, ParsedAction liftedAction) {

        int numberEffActions = liftedAction.getEffects().getChildren().size();
        if (numberEffActions == 0 && liftedAction.getEffects().getSymbol() != null) {
            numberEffActions = 1;
        }

        // Iterate over all positive effects of the parsedAction
        for (int posEffId = 0; posEffId < numberEffActions; posEffId++) {

            Expression<String> posEff;
            if (numberEffActions > 1) {
                posEff = liftedAction.getEffects().getChildren().get(posEffId);
            } else {
                posEff = liftedAction.getEffects();
            }

            // If it is a negative effect, pass this effect
            if (posEff.getConnector().getImage().equals("not")) {
                continue;
            }

            // Get the name of the predicate of the positive effect of the action
            String posEffPredName = posEff.getSymbol().getValue();

            // Check if this positive effect can be unified by an atom candidate
            for (AtomCandidate atomCandidate : candidate.mutexGroup) {

                if (!atomCandidate.predSymbolName.equals(posEffPredName)) {
                    continue;
                }

                System.out.println("Add effect " + posEffPredName);

                // Here, we should clear all the candidate variables values of arguments
                for (AtomVariable var : candidate.variables) {
                    var.value = null;
                }

                // Now, we must ground the args of the atomCandidate to a specific value to
                // unify with the positive effect of the action
                if (!unifyLiftedFact(liftedAction, posEff, atomCandidate, problem, false)) {
                    System.out.println("Cannot unify");
                    continue;
                }

                // To see if this action is really unbalanced, we must now iterate over all the
                // delete effects of the action and see
                // if we can unify a delete effect of the action with one of the atom candidate

                // Create a variable which will check if this action positive effect predicate
                // is balanced with a negative effect predicate of the action
                boolean posEffIsBalanced = false;
                // Iterate over all negative effects of the parsedAction
                for (int negEffId = 0; negEffId < numberEffActions; negEffId++) {

                    // If it is not a negative effect, pass this effect
                    if (!((numberEffActions > 1
                            && liftedAction.getEffects().getChildren().get(negEffId).getConnector().getImage()
                                    .equals("not"))
                            || (numberEffActions == 1 && liftedAction.getEffects().getConnector().getImage()
                                    .equals("not")))) {
                        continue;
                    }

                    Expression<String> negEff;

                    if (numberEffActions > 1) {
                        negEff = liftedAction.getEffects().getChildren().get(negEffId).getChildren().get(0);
                    } else {
                        negEff = liftedAction.getEffects().getChildren().get(0);
                    }

                    // Get the name of the negative predicate
                    String negEffPredName = negEff.getSymbol().getValue();

                    // Check if this negative effect can be unified by an atom candidate (e.g: the
                    // add effect if balanced)
                    for (AtomCandidate atomCandidate2 : candidate.mutexGroup) {

                        if (!atomCandidate2.predSymbolName.equals(negEffPredName)) {
                            continue;
                        }
                        System.out.println("Del effect " + posEffPredName);
                        // Now we can check if we can ground the atom condidate to the value of the
                        // predicate

                        if (unifyLiftedFact(liftedAction, negEff, atomCandidate2, problem, true)) {

                            // TODO
                            // we also must check that there is a precondition exactly matching the delete
                            // effect so we can be sure that the delete effect is present in the state the
                            // action is applied on, i.e., that the delete effect really balances the add
                            // effect.

                            // If we have succeeded to unify, continue to the next positive effect of the
                            // action (since we already know that this positive effect is balanced)
                            posEffIsBalanced = true;
                            break;
                        }

                        // If we have succeeded to unify, continue to the next positive effect of the
                        // action (since we already know that this positive effect is balanced)
                        // if (successToUnify) {
                        // posEffIsBalanced = true;
                        // break;
                        // }
                    }

                    // If the positive predicat is balanced, continue to check if the next positive
                    // predicate is balanced
                    if (posEffIsBalanced) {
                        break;
                    }
                    // Else, check if the actin is balanced with the next negative effect of the
                    // action
                }

                // If no negative effect can balanced this action...
                if (!posEffIsBalanced) {
                    // Some cleaning at the end
                    for (AtomVariable var : candidate.variables) {
                        var.value = null;
                    }

                    System.out.println("Action is unbalanced !");
                    // Refine the variable type
                    System.out.println("Refine variable type\n");
                    refineVariableTypeLifted(candidate, atomCandidate, liftedAction, posEff, problem);

                    System.out.println("Refine extended");
                    refineExtend(candidate, problem, liftedAction);
                    return false;
                }
            }
        }

        // Some cleaning at the end
        for (AtomVariable var : candidate.variables) {
            var.value = null;
        }
        // if all positive effects are balanced with negative effects then the action is
        // balanced
        return true;
    }

    /**
     * 
     * Determines if a lifted action is too heavy with a given candidate and
     * problem.
     * (The weight of a candidate is the sum of all the add effects of the action
     * that can be unified with the candidate. An action is too heavy for a
     * candidate if its
     * weight
     * is > 2).
     * 
     * @param candidate    The candidate to check against the lifted action
     * @param problem      The problem the lifted action belongs to
     * @param liftedAction The lifted action to check for weightiness
     * 
     * @return true if the lifted action is balanced with the given candidate, false
     *         otherwise
     */
    private static boolean isActionTooHeavy(Candidate candidate, Problem problem, ParsedAction liftedAction) {

        int numberEffActions = liftedAction.getEffects().getChildren().size();
        if (numberEffActions == 0 && liftedAction.getEffects().getSymbol() != null) {
            numberEffActions = 1;
        }

        if (numberEffActions <= 1) {
            return false;
        }

        // Iterate over all positive effects of the parsedAction
        for (int posEffId = 0; posEffId < liftedAction.getEffects().getChildren().size(); posEffId++) {

            Expression<String> posEff = liftedAction.getEffects().getChildren().get(posEffId);

            // If it is a negative effect, pass this effect
            if (posEff.getConnector().getImage().equals("not")) {
                continue;
            }

            // Get the name of the predicate of the positive effect of the action
            String posEffPredName = posEff.getSymbol().getValue();

            // Check if this positive effect can be unified by an atom candidate
            for (AtomCandidate atomCandidate : candidate.mutexGroup) {

                if (!atomCandidate.predSymbolName.equals(posEffPredName)) {
                    continue;
                }

                // Unify the positive predicate with the atom candidate
                // Here, we should clear all the candidate variables values of arguments
                for (AtomVariable var : candidate.variables) {
                    var.value = null;
                }

                // Now, we must ground the args of the atomCandidate to a specific value to
                // unify with the positive effect of the action
                if (!unifyLiftedFact(liftedAction, posEff, atomCandidate, problem, false)) {
                    continue;
                }

                // Now, we must check if another add action can be unified at the same time
                // Now, iterate over the remaining add effects of the action and check if we can
                // unify another fact (if this happenend, it means our candidate is too heavy)
                for (int posEffId2 = posEffId + 1; posEffId2 < liftedAction.getEffects().getChildren()
                        .size(); posEffId2++) {

                    Expression<String> posEff2 = liftedAction.getEffects().getChildren().get(posEffId2);

                    // If it is a negative effect, pass this effect
                    if (posEff2.getConnector().getImage().equals("not")) {
                        continue;
                    }

                    // Get the name of the predicate of the positive effect of the action
                    String posEffPredName2 = posEff2.getSymbol().getValue();

                    for (AtomCandidate atomCandidate2 : candidate.mutexGroup) {

                        if (!atomCandidate2.predSymbolName.equals(posEffPredName2)) {
                            continue;
                        }

                        if (unifyLiftedFact(liftedAction, posEff2, atomCandidate2, problem, false)) {
                            // That's a problem, we can unify multiple facts with the atoms candidates, it
                            // means that this is not a mutex... (weight too heavy, at least = 2)
                            // Let's make an refinement
                            System.out.println("Action: " + prettyDisplayLiftedAction(liftedAction, problem)
                                    + " is too heavy for the candidate !\n");
                            refineTooHeavyAction();
                            refineHeavyAction(candidate, liftedAction, atomCandidate, atomCandidate2, posEff, posEff2,
                                    problem);
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    private static boolean isAnyActionTooHeavy(Candidate candidate, Problem problem) {

        // Iterate over each action in a lifted way
        for (ParsedAction action : problem.getParsedProblem().getActions()) {
            System.out.println(prettyDisplayLiftedAction(action, problem));
            if (isActionTooHeavy(candidate, problem, action)) {
                return true;
            }
        }
        return false;
    }

    private static boolean isAnyActionUnbalanced(Candidate candidate, Problem problem) {
        // Iterate over each action in a lifted way
        for (ParsedAction action : problem.getParsedProblem().getActions()) {
            System.out.println(prettyDisplayLiftedAction(action, problem));
            if (!isActionBalanced(candidate, problem, action)) {
                return true;
            }
        }
        return false;
    }

    private static boolean pddlTypeIsParent(String nameTypeParent, String nameTypeChild, Problem problem) {

        return dictTypeToParentTypes.get(nameTypeChild).contains(nameTypeParent);
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

    private static Queue<Candidate> initialCandicatesAllVarsCounted(Problem problem) {

        // Initialize our array which will contains all the invariantCandidate
        Queue<Candidate> invariantCandidateArr = new LinkedList<Candidate>();

        // Iterate over all lifted predicate
        for (int predSymbolId = 0; predSymbolId < problem.getPredicateSymbols().size(); predSymbolId++) {

            // Verify that this predicate appear at least in the effect of one action. If
            // not, pass this predicate
            // (so one action as this predicate symbols as effect)

            String predicateName = problem.getPredicateSymbols().get(predSymbolId);
            if (staticPredicates.contains(predicateName)) {
                continue;
            }

            // Create the candidate which contains this mutex group
            Candidate candidate = new Candidate();

            AtomCandidate pddlLiftedMutexGroup = pddlLiftedMGroupInitCandFromPred(problem, candidate, predSymbolId);

            // Each candidate only contains one predicate candidate at the beginning (and
            // all parameter of this predicate candidate are counted)
            candidate.mutexGroup.add(pddlLiftedMutexGroup);

            // System.out.println(candidate);

            invariantCandidateArr.add(candidate);
        }
        return invariantCandidateArr;
    }

    private static AtomCandidate pddlLiftedMGroupInitCandFromPred(Problem problem, Candidate candidate, int predId) {

        // Create our InvariantCandidate predicate (each invariant candidate has only
        // one predicate at
        // the beginning of the algorithm with each arguement of this predicate in
        // counted variable)
        AtomCandidate invariantCondidateMutexGroup = new AtomCandidate(candidate,
                problem.getPredicateSymbols().get(predId));

        // Get the signature of the predicate
        List<Symbol<Integer>> predSignature = problem.getPredicateSignatures().get(predId);

        // Number of params of the predicate
        int paramSize = predSignature.size();

        // Iterate over the parameters of this predicate
        for (int paramId = 0; paramId < paramSize; paramId++) {

            // Create a new variable of type counted variable
            int typeId = predSignature.get(paramId).getValue();
            String typeName = problem.getTypes().get(typeId);
            AtomVariable atomVariable = new AtomVariable(typeName, true);
            // Add it to the set of all the variables of this candidate
            candidate.variables.add(atomVariable);

            // Add it as well as the parameter Id
            invariantCondidateMutexGroup.paramsId.add(paramId);
        }

        // PddlCondAtom atom = new PddlCondAtom(predId, paramSize);
        // invariantCondidate.cond = atom;

        return invariantCondidateMutexGroup;

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

    public static void preprocessingComputeDictObjectNameToType(Problem problem) {

        dictObjNameToType = new HashMap<>();
        for (TypedSymbol<String> obj : problem.getParsedProblem().getConstants()) {
            dictObjNameToType.put(obj.getValue(), obj.getTypes().get(0).getValue());
        }
    }

    /**
     * Compute all the parents name type and children name type of each type. Fill
     * the two map dictTypeToParentTypes and dictTypeToChildTypes
     * 
     * @param problem
     */
    public static void preprocessingComputeAllParentsAndChildrenEachTypes(Problem problem) {

        // Initialize our 2 maps + create A map from the name of the type to the object
        Map<String, TypedSymbol<String>> dictTypeNameToObj = new HashMap<>();
        dictTypeToParentTypes = new HashMap<>();
        dictTypeToChildTypes = new HashMap<>();

        for (TypedSymbol<String> typeObj : problem.getParsedProblem().getTypes()) {
            String typeName = typeObj.getValue();
            dictTypeToParentTypes.put(typeName, new HashSet<String>());
            dictTypeToChildTypes.put(typeName, new HashSet<String>());
            dictTypeNameToObj.put(typeName, typeObj);
        }

        // Now iterate over each object to set their parent. And once we have
        // them, reiterate to find all the children
        // Not optimal, but we do not care, as there are never too much different
        // objects

        for (TypedSymbol<String> type : problem.getParsedProblem().getTypes()) {
            recursiveFindAllParentOfType(dictTypeToParentTypes.get(type.getValue()), type, dictTypeNameToObj);
        }

        // Now, that we have all the parents of each type, we can compute the children
        for (String typeParent : dictTypeToParentTypes.keySet()) {
            for (String typeChild : dictTypeToParentTypes.keySet()) {
                if (dictTypeToParentTypes.get(typeChild).contains(typeParent)) {
                    dictTypeToChildTypes.get(typeParent).add(typeChild);
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

    public static void removeSubProvedCandidates() {

        HashSet<Candidate> candidatesToPrune = new HashSet<Candidate>();

        // Iterate over each pair of proved candidates
        for (Candidate candidateProved1 : candidatesProved) {
            for (Candidate candidateProved2 : candidatesProved) {

                if (candidateProved1 != candidateProved2 
                && !candidatesToPrune.contains(candidateProved1) 
                && !candidatesToPrune.contains(candidateProved2)) {

                    
                    // Check if both candidates have the same set of predicates name
                    // And each argument of each predicate name have the same type
                    Candidate potentialSubCandidate;
                    Candidate potentialDadCandidate;
                    
                    // For a candidate to be a subcandidate to another candidate, it means that all its predicate are
                    // among the bigger predicate and each argument of the predicate are among the argument of the predicate of the parent candidate
                    if (candidateProved1.mutexGroup.size() > candidateProved2.mutexGroup.size()) {
                        potentialDadCandidate = candidateProved1;
                        potentialSubCandidate = candidateProved2;
                    } else {
                        potentialDadCandidate = candidateProved2;
                        potentialSubCandidate = candidateProved1;
                    }

                    boolean isSubCandidate = true;

                    for (AtomCandidate atomCandidateSon : potentialSubCandidate.mutexGroup) {
                        
                        String sonPredicateName = atomCandidateSon.predSymbolName;

                        boolean parentHasThisPredicate = false;

                        
                        // Get the parent atom candidate associated
                        for (AtomCandidate atomCandidateDad : potentialDadCandidate.mutexGroup) {
                            if (atomCandidateDad.predSymbolName.equals(sonPredicateName)) {

                                parentHasThisPredicate = true;
                                
                                // Now, we must check if for each argument:
                                // arg Son CountedVar => arg parent CountedVar
                                for (int argi = 0; argi < atomCandidateDad.paramsId.size(); argi++) {

                                    AtomVariable varSon = atomCandidateSon.candidateParent.variables.get(atomCandidateSon.paramsId.get(argi));
                                    AtomVariable varDad = atomCandidateDad.candidateParent.variables.get(atomCandidateDad.paramsId.get(argi));
                                    if (!(varDad.typeName.equals(varSon.typeName) || dictTypeToChildTypes.get(varDad.typeName).contains(varSon.typeName))
                                    || (varSon.isCountedVar && !varDad.isCountedVar)) {

                                        isSubCandidate = false;
                                    }
                                }
                            }
                        }

                        if (!parentHasThisPredicate) {
                            isSubCandidate = false;
                            break;
                        }
                    }

                    if (!isSubCandidate) {
                        continue;
                    }
                    else {
                        candidatesToPrune.add(potentialSubCandidate);
                    }
                }
            }
        }

        System.out.println("Candidates to prune:");
        for (Candidate candidateToPrune : candidatesToPrune) {
            System.out.println(candidateToPrune.getUniqueStringRepresentation());
        }
        System.out.println("-------------");
        candidatesProved.removeAll(candidatesToPrune);
    }

    public static Vector<GroundCandidate> groundMutexes(Problem problem, HashSet<Candidate> provedCandidates) {

        Vector<GroundCandidate> allGroundCandidates = new Vector<>();

        for (int fluentIdx = 0; fluentIdx < problem.getFluents().size(); fluentIdx++) {
            Fluent fluent = problem.getFluents().get(fluentIdx);
            boolean canUnifyWithAtLeastOneCandidate = false;
            String namePredicate = problem.getPredicateSymbols().get(fluent.getSymbol());

            if (staticPredicates.contains(namePredicate)) {
                continue;
            }

            // Iterate over all proved candidates
            for (Candidate candidate : provedCandidates) {

                // Get the atom Candidate which can try to unify with this fluent (if there is
                // one)
                for (AtomCandidate atomCandidate : candidate.mutexGroup) {
                    if (atomCandidate.predSymbolName.equals(namePredicate)) {

                        Vector<String> valueFixedVariables = new Vector<String>();

                        // Check if each argument of this fluent is equal of is a subtype of the
                        // corresponding atomVariable
                        // of the atomCandidate of the candidate
                        boolean canUnify = true;
                        for (int argId = 0; argId < atomCandidate.paramsId.size(); argId++) {
                            // Get the name of the object
                            String argPredObj = problem.getConstantSymbols().get(fluent.getArguments()[argId]);
                            String typeArgPredicate = dictObjNameToType.get(argPredObj);
                            AtomVariable var = candidate.variables.get(atomCandidate.paramsId.get(argId));
                            if (!var.typeName.equals(typeArgPredicate)
                                    && !pddlTypeIsParent(var.typeName, typeArgPredicate, problem)) {
                                canUnify = false;
                            } else {
                                if (!var.isCountedVar) {
                                    valueFixedVariables.addElement(argPredObj);
                                }
                            }
                        }
                        if (canUnify) {

                            canUnifyWithAtLeastOneCandidate = true;

                            // Get the ground candidate associate (or create it if it does not exist)
                            boolean groundCandidateFound = false;
                            for (GroundCandidate groundCandidate : allGroundCandidates) {
                                if (groundCandidate.schemaCandidate.equals(candidate.getUniqueStringRepresentation())
                                        && groundCandidate.valueFixedVars.equals(valueFixedVariables)) {
                                    groundCandidateFound = true;
                                    groundCandidate.fluentsMask.set(fluentIdx, true);
                                }
                            }

                            if (!groundCandidateFound) {
                                // Create the new ground candidate
                                GroundCandidate g = new GroundCandidate(candidate.getUniqueStringRepresentation(),
                                        valueFixedVariables, problem);
                                g.fluentsMask.set(fluentIdx, true);
                                allGroundCandidates.add(g);
                            }
                            break;
                        }
                    }
                }
            }

            if (!canUnifyWithAtLeastOneCandidate) {
                // Create a mutex with only one value in this specific case
                GroundCandidate g = new GroundCandidate(prettyDisplayFluent(fluent, problem), new Vector<String>(),
                        problem);
                g.fluentsMask.set(fluentIdx, true);
                allGroundCandidates.add(g);
            }
        }

        // Now, we can run the greedy algorithm of Helmert to prevent overlapping of predicate
        // (predicate in multiple mutexes)
        Vector<GroundCandidate> finalMutexedGroup = new Vector<GroundCandidate>();
        while (allGroundCandidates.size() > 0) {
            // Get the ground candidate with the maximal cardinality
            int maxCardinality = 0;
            GroundCandidate groundCandidateWithMaxCardinality = null;
            for (GroundCandidate groundCandidate : allGroundCandidates) {
                if (groundCandidate.fluentsMask.cardinality() > maxCardinality) {
                    maxCardinality = groundCandidate.fluentsMask.cardinality();
                    groundCandidateWithMaxCardinality = groundCandidate;
                }
            }

            allGroundCandidates.remove(groundCandidateWithMaxCardinality);

            // Add this ground candidate to the hashSet
            finalMutexedGroup.add(groundCandidateWithMaxCardinality);
            // Remove all the fluents that can be taken by this ground candidate from the
            // other ground candidate
            Iterator<GroundCandidate> iterator = allGroundCandidates.iterator();
            while (iterator.hasNext()) {
                GroundCandidate groundCandidate = iterator.next();
                groundCandidate.fluentsMask.andNot(groundCandidateWithMaxCardinality.fluentsMask);
                // If all the fluents of an atom candidate have already been taken by a bigger
                // groundCandidate
                if (groundCandidate.fluentsMask.cardinality() == 0) {
                    iterator.remove();
                }
            }
        }

        // System.out.println("===========================");
        // for (GroundCandidate groundCandidate : finalMutexedGroup) {
        //     System.out
        //             .println(groundCandidate.schemaCandidate + " (" + groundCandidate.fluentsMask.cardinality() + ")");
        //     int idx = groundCandidate.fluentsMask.nextSetBit(0);
        //     while (idx != -1) {
        //         System.out.println(prettyDisplayFluent(problem.getFluents().get(idx), problem));
        //         idx = groundCandidate.fluentsMask.nextSetBit(idx + 1);
        //     }
        //     System.out.println("===========================");
        // }
        // System.out.println("===========================");

        // System.out.println("Number of mutexes: " + finalMutexedGroup.size());

        return finalMutexedGroup;
    }

}

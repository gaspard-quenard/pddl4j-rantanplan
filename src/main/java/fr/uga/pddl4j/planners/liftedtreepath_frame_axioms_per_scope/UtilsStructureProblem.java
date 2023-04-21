package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Vector;

import fr.uga.pddl4j.parser.Connector;
import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.NamedTypedList;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.TypedSymbol;
import fr.uga.pddl4j.parser.SAS_Plus.AtomCandidate;
import fr.uga.pddl4j.parser.SAS_Plus.AtomVariable;
import fr.uga.pddl4j.parser.SAS_Plus.Candidate;
import fr.uga.pddl4j.problem.Problem;
import org.apache.commons.lang3.tuple.Pair;

public class UtilsStructureProblem {

    // A dictionary which map the name of a type to all the parent of this type
    public static Map<String, HashSet<String>> dictTypeToParentTypes;
    // A dictionary which map the name of a type to all the children of this type
    public static Map<String, HashSet<String>> dictTypeToChildTypes;
    // A set of all the static predicates
    public static HashSet<String> staticPredicates;
    // A dictionary which map the name of a type to all the objects of this type
    public static Map<String, Vector<String>> dictTypeToObjects;
    // A dictionary which map the name of an object to its type
    public static Map<String, String> dictObjNameToType;

    // All predicates of the problem ordered by their name
    private static ArrayList<String> predicatesName;

    private static Map<String, ArrayList<String>> predicateToTypeParams;

    private static Map<String, Integer> predicateToNumberInstanciations;

    private static Map<String, HashSet<ArrayList<String>>> mapStaticPredicatesToObjects;

    private static int nbPredicates;

    private static ArrayList<ArrayList<Integer>> cliques;

    // Indicate for each predicate where is has been last defined (for the time step)
    public static int[] predicateIdToLastDefinePredicate;
    // Indicate for each predicate its ID into its clique (if it is in a clique, else -1)
    public static int[] predicateIdToCliqueId;
    // For each clique, map a list of parameters to the unique ID of this list of parameters
    public static HashMap<ArrayList<String>, Integer>[] arrayParamsToParamsIdForEachClique;
    // For each clique, map a unique ID of a list of values to the unique ID of this list of values
    public static HashMap<Integer, Integer>[] arrayValuesToValuesIdForEachClique;

    public static SASPredicate[] predicatesSAS;

    // Indicate for each clique Id, the list of the subclique in this clique (e.g: for clique at V0 C0, we have the subclique at truck0 C0)
    static ArrayList<HashSet<Clique>> subCliques;



    public static void initialize(Problem problem, ArrayList<Candidate> cliquesLifted, ArrayList<ArrayList<Integer>> cliques) {

        // For each type, find all its parents types and children types
        UtilsStructureProblem.preprocessingComputeAllParentsAndChildrenEachTypes(problem);


        // Find the type of each object
        UtilsStructureProblem.dictTypeToObjects = new HashMap<String, Vector<String>>();
        for (TypedSymbol<String> type : problem.getParsedProblem().getTypes()) {
            String typeName = type.getValue();
            UtilsStructureProblem.dictTypeToObjects.put(typeName, new Vector<String>());
        }

        // Now iterate over each object to get the type
        for (TypedSymbol<String> obj : problem.getParsedProblem().getConstants()) {
            String nameObj = obj.getValue();
            String typeObj = obj.getTypes().get(0).getValue();
            System.out.println(nameObj + " " + typeObj);
            UtilsStructureProblem.dictTypeToObjects.get(typeObj).add(nameObj);
            // We also need to add the object to all its parents types
            for (String parentType : UtilsStructureProblem.dictTypeToParentTypes.get(typeObj)) {
                UtilsStructureProblem.dictTypeToObjects.get(parentType).add(nameObj);
            }
        }

        // Find all static predicates
        UtilsStructureProblem.staticPredicates = preprocessingComputeStaticPredicates(problem);

        // Determine all the predicates of the problem
        UtilsStructureProblem.predicatesName = new ArrayList<String>();
        UtilsStructureProblem.predicateToTypeParams = new HashMap<String, ArrayList<String>>();

        for (NamedTypedList pred : problem.getParsedProblem().getPredicates()) {

            String namePredicate = pred.getName().getValue();
            predicatesName.add(namePredicate);
            // Find all the parameters of this predicate
            ArrayList<String> paramsType = new ArrayList<String>();
            for (TypedSymbol<String> argPred : pred.getArguments()) {
                // Get the type of this parameter
                String argTypeName = argPred.getTypes().get(0).getValue();
                paramsType.add(argTypeName);
            }
            UtilsStructureProblem.predicateToTypeParams.put(namePredicate, paramsType);
        }

        UtilsStructureProblem.getNumberInstantiationEachPredicate(problem);

        // Now, that we have the number of predicate, we can initialize the structure of the predicates
        predicatesSAS = new SASPredicate[UtilsStructureProblem.nbPredicates];

        initializeAllPredicates(problem);

        // Initialize all the predicates

        // Check if the function getPredicateID is correct
        
        // for (String predicateName : UtilsStructureProblem.predicatesName) {
        //     ArrayList<String> paramsValue = new ArrayList<String>();
        //     for (String paramType : UtilsStructureProblem.predicateToTypeParams.get(predicateName)) {
        //         paramsValue.add(UtilsStructureProblem.dictTypeToObjects.get(paramType).get(0));
        //     }
        //     int predicateID = UtilsStructureProblem.getPredicateID(predicateName, paramsValue);
        //     System.out.println(predicateName + " " + paramsValue + " " + predicateID);
        // }

        // Finally, indicate for each predicate where is has been last defined (for now, there all have been defined in the initial state)
        predicateIdToLastDefinePredicate = new int[UtilsStructureProblem.nbPredicates];

        if (LiftedTreePathConfig.useSASPlusEncoding) {

            UtilsStructureProblem.cliques = cliques;

            // Create our array which will indicate for each predicate its ID into its clique (if it is in a clique, else -1)
            predicateIdToCliqueId = new int[UtilsStructureProblem.nbPredicates];

            // Initialize all the values to -1
            for (int i = 0; i < UtilsStructureProblem.nbPredicates; i++) {
                predicateIdToCliqueId[i] = -1;
            }

            // predicatesSAS = new SASPredicate[UtilsStructureProblem.nbPredicates];

            // Create our subclique 
            subCliques = new ArrayList<HashSet<Clique>>();
            for (int i = 0; i < cliquesLifted.size(); i++) {
                subCliques.add(new HashSet<Clique>());
            }

            // Now, for each predicate, we need to find its clique
            UtilsStructureProblem.findCliqueForAllPredicates(problem, cliquesLifted);
        }
        int a = 0;
    }

    public static HashSet<ArrayList<String>> getAllObjectsForStaticPredicate(String predicateName) {
        return UtilsStructureProblem.mapStaticPredicatesToObjects.get(predicateName);
    }

    public static void findCliqueForAllPredicates(Problem problem, ArrayList<Candidate> cliques) {
        
        // Iterate over all cliques
        for (Candidate clique : cliques) {

            int idxClique = cliques.indexOf(clique);

            int numberCountedVar = 0;

            // First, find the type of all params and values of this clique
            ArrayList<String> paramsType = new ArrayList<String>();
            ArrayList<String> valuesType = new ArrayList<String>();

            for (AtomVariable var : clique.variables) {
                if (var.isCountedVar) {
                    // This is a value
                    valuesType.add(var.typeName);
                    numberCountedVar++;
                } else {
                    // This is a parameter
                    paramsType.add(var.typeName);
                }
            }

            // Create an array containing all the objects for each parameter
            ArrayList<Vector<String>> paramsObjects = new ArrayList<Vector<String>>();
            for (String paramType : paramsType) {
                paramsObjects.add(UtilsStructureProblem.dictTypeToObjects.get(paramType));
            }

            // Create an array containing all the objects for each value
            ArrayList<Vector<String>> valuesObjects = new ArrayList<Vector<String>>();
            for (String valueType : valuesType) {
                valuesObjects.add(UtilsStructureProblem.dictTypeToObjects.get(valueType));
            }

            // Get all the combinations of objects for each parameter
            ArrayList<ArrayList<String>> paramsCombinations = UtilsStructureProblem.getAllPossibleCombinaisons(paramsObjects);
            if (paramsCombinations.size() == 0) {
                paramsCombinations.add(new ArrayList<String>());
            }

            // Get all the combinations of objects for each value
            ArrayList<ArrayList<String>> valuesCombinations = UtilsStructureProblem.getAllPossibleCombinaisons(valuesObjects);
            if (valuesCombinations.size() == 0) {
                valuesCombinations.add(new ArrayList<String>());
            }

            HashSet<String> predicatesAlreadySeen = new HashSet<String>();

            for (ArrayList<String> params : paramsCombinations) {

                predicatesAlreadySeen.clear();

                // Create our clique object
                Clique cliqueSAS = new Clique(idxClique, clique, params);

                // Add it in our list of subcliques
                subCliques.get(idxClique).add(cliqueSAS);

                int valueIntegerClique = 1; // We start from 1 because 0 is for "None of those"

                // Now iterate over each predicate of this clique
                for (AtomCandidate mutex : clique.mutexGroup) {

                    String predicateName = mutex.predSymbolName;

                    // Get all the values relevant to this predicates
                    // ArrayList<Vector<String>> relevantValues = new ArrayList<Vector<String>>(numberCountedVar);
                    // for (int i = 0; i < numberCountedVar; i++) {
                    //     relevantValues.add(new Vector<String>());
                    // }

                    // // Iterate over all the parameters of this predicate, and if it is a counted variable, add all the objects of this type (and subtypes) to the list of relevant values at the right position
                    // for (Integer paramId : mutex.paramsId) {
                    //     AtomVariable var = clique.variables.get(paramId); 
                    //     if (var.isCountedVar) {
                    //         relevantValues.get(var.idInAtomCandidate).addAll(UtilsStructureProblem.dictTypeToObjects.get(var.typeName));
                    //     }
                    // }


                    for (int valuesIdx = 0; valuesIdx < valuesCombinations.size(); valuesIdx++) {
                        ArrayList<String> values = valuesCombinations.get(valuesIdx);

                        // Get the ground the predicate of the mutex with the params and values
                        String groundFluent = UtilsStructureProblem.getSASGroundPredicateFromParamsValues(mutex, params, values);
                        ArrayList<String> paramsGroundFluent = UtilsStructureProblem.getPredicateParametersFromParamsValuesMutex(mutex, params, values);

                        if (predicatesAlreadySeen.contains(groundFluent)) {
                            continue;
                        }

                        predicatesAlreadySeen.add(groundFluent);
                        Integer idGroundFluent = getPredicateIdFromSASPredicateWithParamsValues(mutex, params, values);

                        // Now, we must indicate that this predicate can belong to this clique and the value it has in this clique
                        SASPredicate sasPredicate = predicatesSAS[idGroundFluent];
                        if (sasPredicate == null) {
                            sasPredicate = new SASPredicate(idGroundFluent, predicateName, groundFluent, paramsGroundFluent);
                        }
                        sasPredicate.addClique(cliqueSAS, valueIntegerClique);

                        // Add this predicate to our list of predicates
                        predicatesSAS[idGroundFluent] = sasPredicate;

                        // Increment the value of the clique
                        valueIntegerClique++;
                    }
                }
                cliqueSAS.setNumberValues(valueIntegerClique);
            }
        }

        int a = 0;
    }

    public static int getPredicateID(String predicateName, ArrayList<String> paramsValue) {

        int predicateID = 0;
        for (String predName : UtilsStructureProblem.predicatesName) {
            if (predName.equals(predicateName)) {
                break;
            }
            predicateID += predicateToNumberInstanciations.get(predName);
        }

        int maxParam = 1;
        for (int paramIdx = 0; paramIdx < paramsValue.size(); paramIdx++) {
            // First, get the type of the parameter

            String paramType = UtilsStructureProblem.predicateToTypeParams.get(predicateName).get(paramIdx);

            // Get all the objects of this type
            Vector<String> objectsOfType = UtilsStructureProblem.dictTypeToObjects.get(paramType);

            // Get the index of the object in the list of objects of this type
            int objectIdx = objectsOfType.indexOf(paramsValue.get(paramIdx));

            // Add the index of the object to the predicate ID
            predicateID += maxParam * objectIdx;

            // Update the maxParam
            maxParam *= UtilsStructureProblem.dictTypeToObjects.get(paramType).size();
        }

        return predicateID;
    }

    public static int getLastTimePredicateDefined(String predicateName, ArrayList<String> paramsValue) {
        int predicateID = UtilsStructureProblem.getPredicateID(predicateName, paramsValue);
        SASPredicate pred = predicatesSAS[predicateID];
        // Two case, either we are in SAS plus mode or not
        // If not in SASPlus mode, we just return the last time this predicate was defined
        // If we are in SASPLus mode, we check all the clique this predicate is among, and take the latest defined clique
        if (!LiftedTreePathConfig.useSASPlusEncoding || pred.cliques.size() == 0) {
            return pred.getLastTimePredicateWasDefined();
        } else {
            int lastTimeDefined = 0;
            for (Clique clique : pred.cliques) {
                if (clique.getLastTimeCliqueWasDefined() > lastTimeDefined) {
                    lastTimeDefined = clique.getLastTimeCliqueWasDefined();
                }
            }
            return lastTimeDefined;
        }
    }

    public static void updateLastTimePredicateDefined(String predicateName, ArrayList<String> paramsValue, int timeStep) {
        int predicateID = UtilsStructureProblem.getPredicateID(predicateName, paramsValue);
        predicateIdToLastDefinePredicate[predicateID] = timeStep;
    }

    public static void resetLastTimePredicateDefined() {
        for (int i = 0; i < predicateIdToLastDefinePredicate.length; i++) {
            predicateIdToLastDefinePredicate[i] = 0;
        }
    }



/**
     * Compute all the parents name type and children name type of each type. Fill
     * the two map dictTypeToParentTypes and dictTypeToChildTypes
     * 
     * @param problem
     */
    private static void preprocessingComputeAllParentsAndChildrenEachTypes(Problem problem) {

        // Initialize our 2 maps + create A map from the name of the type to the object
        Map<String, TypedSymbol<String>> dictTypeNameToObj = new HashMap<>();
        UtilsStructureProblem.dictTypeToParentTypes = new HashMap<>();
        UtilsStructureProblem.dictTypeToChildTypes = new HashMap<>();

        for (TypedSymbol<String> typeObj : problem.getParsedProblem().getTypes()) {
            String typeName = typeObj.getValue();
            UtilsStructureProblem.dictTypeToParentTypes.put(typeName, new HashSet<String>());
            UtilsStructureProblem.dictTypeToChildTypes.put(typeName, new HashSet<String>());
            dictTypeNameToObj.put(typeName, typeObj);
        }

        // Now iterate over each object to set their parent. And once we have
        // them, reiterate to find all the children
        // Not optimal, but we do not care, as there are never too much different
        // objects

        for (TypedSymbol<String> type : problem.getParsedProblem().getTypes()) {
            recursiveFindAllParentOfType(UtilsStructureProblem.dictTypeToParentTypes.get(type.getValue()), type, dictTypeNameToObj);
        }

        // Now, that we have all the parents of each type, we can compute the children
        for (String typeParent : UtilsStructureProblem.dictTypeToParentTypes.keySet()) {
            for (String typeChild : UtilsStructureProblem.dictTypeToParentTypes.keySet()) {
                if (UtilsStructureProblem.dictTypeToParentTypes.get(typeChild).contains(typeParent)) {
                    UtilsStructureProblem.dictTypeToChildTypes.get(typeParent).add(typeChild);
                }
            }
        }
    }

    private static void recursiveFindAllParentOfType(HashSet<String> parents, TypedSymbol<String> type,
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

    public static void findAllPredicateTrueAndFalseForInitialState(Problem problem, HashSet<String> predicateTrueAtInitState, HashSet<String> predicateFalseAtInitState) {

        // First, determinate all the predicates that are true at the initial state
        HashSet<String> predicateTrueAtInitStateTemp = new HashSet<String>();

        for (Expression<String> initPred : problem.getParsedProblem().getInit()) {

            // If the connetor is NOT, then the predicate is false
            // we can ignore it
            if (initPred.getConnector().equals(Connector.NOT)) {
                continue;
            }
            
            // Get the predicate name
            String predicateName = initPred.getSymbol().getValue();

            // If this is a static predicate, we can ignore it
            if (UtilsStructureProblem.staticPredicates.contains(predicateName)) {
                continue;
            }

            // Get the parameters
            ArrayList<String> params = new ArrayList<String>();
            for (int paramIdx = 0; paramIdx < initPred.getArguments().size(); paramIdx++) {
                params.add(initPred.getArguments().get(paramIdx).getValue());
            }

            String fullPredicateName = UtilsStructureProblem.getPredicateNameWithParams(predicateName, params);

            // Add the predicate to the list of true predicates
            predicateTrueAtInitStateTemp.add(fullPredicateName);
        }

        // We need to iterate over all possible predicates
        for (String predicateName : UtilsStructureProblem.predicatesName) {

            // If this is a static predicate, we can ignore it
            if (UtilsStructureProblem.staticPredicates.contains(predicateName)) {
                continue;
            }

            // Then iterate over all possible parameters
            ArrayList<Vector<String>> paramsValue = new ArrayList<Vector<String>>();
            for (String paramType : UtilsStructureProblem.predicateToTypeParams.get(predicateName)) {
                paramsValue.add(UtilsStructureProblem.dictTypeToObjects.get(paramType));
            }

            // Now, we have all the possible parameters, we can iterate over all of them
            // to see if they are true or false
            for (ArrayList<String> combinaison : UtilsStructureProblem.getAllPossibleCombinaisons(paramsValue)) {

                // Construct the ground fluent name with its parameters
                String groundFluentName = UtilsStructureProblem.getPredicateNameWithParams(predicateName, combinaison);

                // Check if the predicate is true or false
                if (predicateTrueAtInitStateTemp.contains(groundFluentName)) {
                    predicateTrueAtInitState.add(groundFluentName + "__0");
                } else {
                    predicateFalseAtInitState.add(groundFluentName + "__0");
                }
            }
        }
    }

    public static void findAllPredicateIdTrueAndFalseForInitialState(Problem problem, HashSet<Integer> predicateIdTrueAtInitState, HashSet<Integer> predicateIdFalseAtInitState) {

        // First, determinate all the predicates that are true at the initial state
        HashSet<Integer> predicateTrueAtInitStateTemp = new HashSet<Integer>();

        for (Expression<String> initPred : problem.getParsedProblem().getInit()) {

            // If the connetor is NOT, then the predicate is false
            // we can ignore it
            if (initPred.getConnector().equals(Connector.NOT)) {
                continue;
            }
            
            // Get the predicate name
            String predicateName = initPred.getSymbol().getValue();

            // If this is a static predicate, we can ignore it
            if (UtilsStructureProblem.staticPredicates.contains(predicateName)) {
                continue;
            }

            // Get the parameters
            ArrayList<String> params = new ArrayList<String>();
            for (int paramIdx = 0; paramIdx < initPred.getArguments().size(); paramIdx++) {
                params.add(initPred.getArguments().get(paramIdx).getValue());
            }

            // String fullPredicateName = UtilsStructureProblem.getPredicateNameWithParams(predicateName, params);
            Integer predicateId = UtilsStructureProblem.getPredicateID(predicateName, params);

            // Add the predicate to the list of true predicates
            predicateTrueAtInitStateTemp.add(predicateId);
        }

        // We need to iterate over all possible predicates
        for (String predicateName : UtilsStructureProblem.predicatesName) {

            // If this is a static predicate, we can ignore it
            if (UtilsStructureProblem.staticPredicates.contains(predicateName)) {
                continue;
            }

            // Then iterate over all possible parameters
            ArrayList<Vector<String>> paramsValue = new ArrayList<Vector<String>>();
            for (String paramType : UtilsStructureProblem.predicateToTypeParams.get(predicateName)) {
                paramsValue.add(UtilsStructureProblem.dictTypeToObjects.get(paramType));
            }

            // Now, we have all the possible parameters, we can iterate over all of them
            // to see if they are true or false
            for (ArrayList<String> combinaison : UtilsStructureProblem.getAllPossibleCombinaisons(paramsValue)) {

                // Construct the ground fluent name with its parameters
                // String groundFluentName = UtilsStructureProblem.getPredicateNameWithParams(predicateName, combinaison);
                Integer groundFluentId = UtilsStructureProblem.getPredicateID(predicateName, combinaison);

                // Check if the predicate is true or false
                if (predicateTrueAtInitStateTemp.contains(groundFluentId)) {
                    predicateIdTrueAtInitState.add(groundFluentId);
                } else {
                    predicateIdFalseAtInitState.add(groundFluentId);
                }
            }
        }
    }
    
    private static void getNumberInstantiationEachPredicate(Problem problem) {
        predicateToNumberInstanciations = new HashMap<>();
        for (NamedTypedList pred : problem.getParsedProblem().getPredicates()) {
            int nbInstanciation = 1;
            // Iterate over each type of each parameter of this predicate
            for (TypedSymbol<String> argPred : pred.getArguments()) {
                // Get the type of this parameter
                String argTypeName = argPred.getTypes().get(0).getValue();
                // See how many objects of this type we have
                nbInstanciation *= UtilsStructureProblem.dictTypeToObjects.get(argTypeName).size();
            }
            predicateToNumberInstanciations.put(pred.getName().getValue(), nbInstanciation);
            UtilsStructureProblem.nbPredicates += nbInstanciation;
        }
    }

    private static void initializeAllPredicates(Problem problem) {
        for (NamedTypedList pred : problem.getParsedProblem().getPredicates()) {
            int nbInstanciation = 1;

            String namePredicate = pred.getName().getValue();

            // Iterate over all the parameters that can take this predicate, and add an entry into our array of SASPRedicate for each of them
            ArrayList<Vector<String>> allValuesForEachParams = new ArrayList<>();

            // Iterate over each type of each parameter of this predicate
            for (TypedSymbol<String> argPred : pred.getArguments()) {
                // Get the type of this parameter
                String argTypeName = argPred.getTypes().get(0).getValue();
                // Add the list of all the objects of this type to the list of all the parameters
                allValuesForEachParams.add(UtilsStructureProblem.dictTypeToObjects.get(argTypeName));
            }

            // Get the list of all the possible parameters
            ArrayList<ArrayList<String>> allPossibleCombinaisons = UtilsStructureProblem.getAllPossibleCombinaisons(allValuesForEachParams);

            for (ArrayList<String> combinaison : allPossibleCombinaisons) {

                // Check the ID of this predicate
                int predicateId = UtilsStructureProblem.getPredicateID(pred.getName().getValue(), combinaison);

                // Construct the ground fluent name with its parameters
                String groundFluentName = UtilsStructureProblem.getPredicateNameWithParams(pred.getName().getValue(), combinaison);
                
                // Create our SASPredicate
                SASPredicate predicate = new SASPredicate(predicateId, namePredicate, groundFluentName, combinaison);

                predicatesSAS[predicateId] = predicate;
            }

        }
    }


    private static HashSet<String> preprocessingComputeStaticPredicates(Problem problem) {

        mapStaticPredicatesToObjects = new HashMap<>();

        HashSet<String> staticPredicates = new HashSet<String>();
        // Iterate over all predicates name
        for (String predicateName : problem.getPredicateSymbols()) {
            if (predicatIsStatic(predicateName, problem)) {
                staticPredicates.add(predicateName);
                mapStaticPredicatesToObjects.put(predicateName, new HashSet<ArrayList<String>>());
            }
        }

        // Now iterate over the initial state to find all the static predicates
        for (Expression<String> initPred : problem.getParsedProblem().getInit()) {

            // We do not care about the predicates that are false at the initial state
            if (initPred.getConnector().equals(Connector.NOT)) {
                continue;
            }

            // Get the predicate name
            String predicateName = initPred.getSymbol().getValue();

            // If the predicate is not static, we do not care about it
            if (!staticPredicates.contains(predicateName)) {
                continue;
            }

            // Get the parameters
            ArrayList<String> params = new ArrayList<String>();
            for (int paramIdx = 0; paramIdx < initPred.getArguments().size(); paramIdx++) {
                params.add(initPred.getArguments().get(paramIdx).getValue());
            }

            // Add the parameters to the list of parameters for this predicate
            mapStaticPredicatesToObjects.get(predicateName).add(params);
        }


        return staticPredicates;
    }


    private static boolean predicatIsStatic(String predicateToCheck, Problem problem) {

        // Iterate over all action of our problem (in a lifted way)
        for (ParsedAction action : problem.getParsedProblem().getActions()) {

            // If the action only have one effect, check if this effect affect the predicate
            if (action.getEffects().getSymbol() != null && action.getEffects().getSymbol().getValue().equals(predicateToCheck)) {
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

    public static String generateRuleConversionPseudoFactToGroundFact(HashSet<CertifiedPredicate> predicateToGround, HashSet<String> cliqueBitsToDefine, HashSet<String> groundFactsToDefine, int timeStep, boolean useLastTimeStepPredicateDefined) {


        StringBuilder ruleToReturn = new StringBuilder();

        for (CertifiedPredicate predToGround : predicateToGround) {

            if (predToGround.isGroundFact()) {
                if (LiftedTreePathConfig.useSASPlusEncoding) {
                    // We must declare this predicate in term of its binary replresentation in the clique bits
                    // Find the last time this ground fact was declared
                    int timeStepPred = timeStep;

                    ArrayList<String> params = new ArrayList<String>();
                    for (int paramIdx = 0; paramIdx < predToGround.scope.size(); paramIdx++) {
                        params.add(predToGround.scope.get(paramIdx).getUniqueName());
                    }

                    int idPredicate = UtilsStructureProblem.getPredicateID(predToGround.predicateName, params);
                    SASPredicate sasPredicate = UtilsStructureProblem.predicatesSAS[idPredicate];

                    if (sasPredicate.cliques.size() == 0) {
                        // Nothing to do here
                        continue;
                    }
                    
                    // Check if this predicate is into one (or multiple cliques)
                    ruleToReturn.append("(assert (=> " + predToGround.toSmt(timeStep) + " (and ");

                    // Iterate over all the cliques of this predicate
                    for (int cliqueIdx = 0; cliqueIdx < sasPredicate.cliques.size(); cliqueIdx++) {

                        // Get the cliqueID 
                        int cliqueID = sasPredicate.cliques.get(cliqueIdx).id;

                        // Get the number of variables in this clique
                        int nbVarInClique = sasPredicate.cliques.get(cliqueIdx).numberValues;

                        // Get the value of this predicate in this clique
                        int valueInClique = sasPredicate.valueInCliques.get(cliqueIdx);

                        // With that, we can get the representation of the predicate in the clique
                        ArrayList<Boolean> valueBitsToRepresentPredInClique = UtilsStructureProblem.getBinaryValueOfPredicateInClique(cliqueID, nbVarInClique, valueInClique);

                        if (useLastTimeStepPredicateDefined) {
                            // Get the last time that the clique containing this predicate was defined
                            timeStepPred = sasPredicate.cliques.get(cliqueIdx).getLastTimeCliqueWasDefined();
                        }

                        for (int varIdx = 0; varIdx < valueBitsToRepresentPredInClique.size(); varIdx++) {
                            String cliqueBitName = "Clique_" + cliqueID + "_bit" + varIdx + "__" + timeStepPred;
                            if (valueBitsToRepresentPredInClique.get(varIdx)) {
                                ruleToReturn.append(cliqueBitName + " ");
                            } else {
                                ruleToReturn.append("(not " + cliqueBitName + ") ");
                            }
                            cliqueBitsToDefine.add(cliqueBitName);
                        }
                    }
                    ruleToReturn.append(")))\n");
                    // groundFactsToDefine.add(predToGround.toSmt(timeStep));
                }
                continue;
            }
                
            // First, we need to generate all the possible combinaisons of values for the variables
            ArrayList<ArrayList<String>> allPossibleCombinations = new ArrayList<ArrayList<String>>();
            for (ScopeVariable scopeVar : predToGround.scope) {
                ArrayList<ArrayList<String>> newAllPossibleCombinations = new ArrayList<ArrayList<String>>();
                for (String object : scopeVar.getPossibleValueVariable()) {
                    if (allPossibleCombinations.isEmpty()) {
                        ArrayList<String> newCombination = new ArrayList<String>();
                        newCombination.add(object);
                        newAllPossibleCombinations.add(newCombination);
                    } else {
                        for (ArrayList<String> combination : allPossibleCombinations) {
                            ArrayList<String> newCombination = new ArrayList<String>();
                            newCombination.addAll(combination);
                            newCombination.add(object);
                            newAllPossibleCombinations.add(newCombination);
                        }
                    }
                }
                allPossibleCombinations = newAllPossibleCombinations;
            }

            // Implement the rule 13 for each combination
            for (ArrayList<String> combinaison : allPossibleCombinations) {
                ruleToReturn.append("(assert (=> (and ");
                StringBuilder groundFact = new StringBuilder();
                groundFact.append(predToGround.predicateName);
                for (int i = 0; i < predToGround.scope.size(); i++) {
                    if (!predToGround.scope.get(i).isConstant()) {
                        ruleToReturn.append(predToGround.scope.get(i).getUniqueName() + "__" + combinaison.get(i) + " ");
                    }
                    groundFact.append("_" + combinaison.get(i));
                }
                // Find the last time this ground fact was declared
                int timeStepPred = timeStep;

                int idPredicate = UtilsStructureProblem.getPredicateID(predToGround.predicateName, combinaison);

                SASPredicate sasPredicate = UtilsStructureProblem.predicatesSAS[idPredicate];

                if (LiftedTreePathConfig.useSASPlusEncoding && sasPredicate.cliques.size() > 0) {

                    if (predToGround.isPositive) {
                        // Check if this predicate is into one (or multiple cliques)
                        ruleToReturn.append(") (= " + predToGround.toSmt(timeStep) + " (and ");
                    } else {
                        // If the predicate is negative, we need to clean all the bits of the cliques of the predicate (set them to 0)
                        // Since, we will have in the effect 
                        ruleToReturn.append(") (= " + predToGround.toSmt(timeStep) + " (or ");
                    }

                    // Iterate over all the cliques of this predicate
                    for (int cliqueIdx = 0; cliqueIdx < sasPredicate.cliques.size(); cliqueIdx++) {

                        // Get the cliqueID 
                        int cliqueID = sasPredicate.cliques.get(cliqueIdx).id;

                        // Get the number of variables in this clique
                        int nbVarInClique = sasPredicate.cliques.get(cliqueIdx).numberValues;

                        // Get the value of this predicate in this clique
                        int valueInClique = sasPredicate.valueInCliques.get(cliqueIdx);

                        // With that, we can get the representation of the predicate in the clique
                        ArrayList<Boolean> valueBitsToRepresentPredInClique = UtilsStructureProblem.getBinaryValueOfPredicateInClique(cliqueID, nbVarInClique, valueInClique);
                        if (!predToGround.isPositive) {
                            // Set all the bits to true
                            for (int i = 0; i < valueBitsToRepresentPredInClique.size(); i++) {
                                valueBitsToRepresentPredInClique.set(i, true);
                            }
                        }

                        if (useLastTimeStepPredicateDefined) {
                            // Get the last time that the clique containing this predicate was defined
                            timeStepPred = sasPredicate.cliques.get(cliqueIdx).getLastTimeCliqueWasDefined();
                        }

                        if (valueBitsToRepresentPredInClique.size() == 0) {
                            int a = 9;
                        }

                        for (int varIdx = 0; varIdx < valueBitsToRepresentPredInClique.size(); varIdx++) {
                            String cliqueBitName = "Clique_" + cliqueID + "_bit" + varIdx + "__" + timeStepPred;
                            if (valueBitsToRepresentPredInClique.get(varIdx)) {
                                ruleToReturn.append(cliqueBitName + " ");
                            } else {
                                ruleToReturn.append("(not " + cliqueBitName + ") ");
                            }
                            cliqueBitsToDefine.add(cliqueBitName);
                        }
                    }
                    ruleToReturn.append("))))\n");
                }
                else {
                    
                    if (useLastTimeStepPredicateDefined) {
                        // timeStepPred = UtilsStructureProblem.getLastTimePredicateDefined(predToGround.predicateName, combinaison);
                        timeStepPred = sasPredicate.getLastTimePredicateWasDefined();
                    }
                    groundFact.append("__" + timeStepPred);
                    ruleToReturn.append(") (= " + predToGround.toSmt(timeStep) + " " + groundFact.toString() + ")))\n");

                    groundFactsToDefine.add(groundFact.toString());
                }
            }
        }
        return ruleToReturn.toString();
    }


    public static String generateRuleConversionPseudoFactToGroundFact(String predicateName, ArrayList<ScopeVariable> scope, int timeStep, boolean useLastTimeStepPredicateDefined) {


        StringBuilder ruleToReturn = new StringBuilder();
                
        // First, we need to generate all the possible combinaisons of values for the variables
        ArrayList<ArrayList<String>> allPossibleCombinations = new ArrayList<ArrayList<String>>();
        for (ScopeVariable scopeVar : scope) {
            ArrayList<ArrayList<String>> newAllPossibleCombinations = new ArrayList<ArrayList<String>>();
            for (String object : scopeVar.getPossibleValueVariable()) {
                if (allPossibleCombinations.isEmpty()) {
                    ArrayList<String> newCombination = new ArrayList<String>();
                    newCombination.add(object);
                    newAllPossibleCombinations.add(newCombination);
                } else {
                    for (ArrayList<String> combination : allPossibleCombinations) {
                        ArrayList<String> newCombination = new ArrayList<String>();
                        newCombination.addAll(combination);
                        newCombination.add(object);
                        newAllPossibleCombinations.add(newCombination);
                    }
                }
            }
            allPossibleCombinations = newAllPossibleCombinations;
        }

        // Implement the rule 13 for each combination
        for (ArrayList<String> combinaison : allPossibleCombinations) {
            ruleToReturn.append("(assert (=> (and ");
            StringBuilder groundFact = new StringBuilder();
            groundFact.append(predicateName);
            for (int i = 0; i < scope.size(); i++) {
                if (!scope.get(i).isConstant()) {
                    ruleToReturn.append(scope.get(i).getUniqueName() + "__" + combinaison.get(i) + " ");
                }
                groundFact.append("_" + combinaison.get(i));
            }
            // Find the last time this ground fact was declared
            int timeStepPred = timeStep;
            if (useLastTimeStepPredicateDefined) {
                timeStepPred = UtilsStructureProblem.getLastTimePredicateDefined(predicateName, combinaison);
            }

            StringBuilder certifiedPredToDisplay = new StringBuilder();
            // if (!this.isPositive) {
            //     certifiedPredToDisplay.append("(not ");
            // }
            certifiedPredToDisplay.append(predicateName);
    
            for (int i = 0; i < scope.size(); i++) {
                certifiedPredToDisplay.append("_" +  scope.get(i).getUniqueName());
            }
    
            certifiedPredToDisplay.append("__" + timeStep);

            if (LiftedTreePathConfig.useSASPlusEncoding) {

                // Find if this ground predicate is into a clique
                
                

            } else {
                groundFact.append("__" + timeStepPred);
                ruleToReturn.append(") (= " + certifiedPredToDisplay.toString() + " " + groundFact.toString() + ")))\n");
            }
            
        }

        return ruleToReturn.toString();
    }


    /**
     * Return all the possible combinaisons of objects for each parameter
     * @param params : the list of all the possible objects for each parameter
     * @return all the possible combinaisons of objects for each parameter
     */
    private static ArrayList<ArrayList<String>> getAllPossibleCombinaisons(ArrayList<Vector<String>> params) {
        ArrayList<ArrayList<String>> allPossibleCombinations = new ArrayList<ArrayList<String>>();
        for (Vector<String> allObjectsPossibleForParam : params) {
            ArrayList<ArrayList<String>> newAllPossibleCombinations = new ArrayList<ArrayList<String>>();
            for (String object : allObjectsPossibleForParam) {
                if (allPossibleCombinations.isEmpty()) {
                    ArrayList<String> newCombination = new ArrayList<String>();
                    newCombination.add(object);
                    newAllPossibleCombinations.add(newCombination);
                } else {
                    for (ArrayList<String> combination : allPossibleCombinations) {
                        ArrayList<String> newCombination = new ArrayList<String>();
                        newCombination.addAll(combination);
                        newCombination.add(object);
                        newAllPossibleCombinations.add(newCombination);
                    }
                }
            }
            allPossibleCombinations = newAllPossibleCombinations;
        }

        return allPossibleCombinations;
    }

    /**
     * Return all the possible combinaisons of objects for each parameter. 
     * @param pred : the certified predicate
     * @return all the possible combinaisons of objects for each parameter (i.e all the possible groundings)
     */
    public static ArrayList<ArrayList<String>> getAllPossibleCombinaisonsOfCertifiedPredicate(CertifiedPredicate pred) {

        ArrayList<HashSet<String>> allObjectsForAllParameters = new ArrayList<HashSet<String>>();


        for (ScopeVariable param : pred.scope) {
            allObjectsForAllParameters.add(param.getPossibleValueVariable());
        }

        // Now we have all the possible objects for each parameter, we need to generate all the possible combinaisons
        ArrayList<ArrayList<String>> allPossibleCombinations = new ArrayList<ArrayList<String>>();
        for (HashSet<String> allObjectsPossibleForParam : allObjectsForAllParameters) {
            ArrayList<ArrayList<String>> newAllPossibleCombinations = new ArrayList<ArrayList<String>>();
            for (String object : allObjectsPossibleForParam) {
                if (allPossibleCombinations.isEmpty()) {
                    ArrayList<String> newCombination = new ArrayList<String>();
                    newCombination.add(object);
                    newAllPossibleCombinations.add(newCombination);
                } else {
                    for (ArrayList<String> combination : allPossibleCombinations) {
                        ArrayList<String> newCombination = new ArrayList<String>();
                        newCombination.addAll(combination);
                        newCombination.add(object);
                        newAllPossibleCombinations.add(newCombination);
                    }
                }
            }
            allPossibleCombinations = newAllPossibleCombinations;
        }

        return allPossibleCombinations;
    }

    /**
     * Generate the full ground fluent name with the parameters
     * @param predicateName : the name of the predicate
     * @param params : the list of all the parameters
     * @return the full ground fluent name with the parameters
     */
    private static String getPredicateNameWithParams(String predicateName, ArrayList<String> params) {
        StringBuilder predicateNameWithParams = new StringBuilder();
        predicateNameWithParams.append(predicateName);
        for (String param : params) {
            predicateNameWithParams.append("_" + param);
        }
        return predicateNameWithParams.toString();
    }


    private static String getSASGroundPredicateFromParamsValues(AtomCandidate mutex, ArrayList<String> params, ArrayList<String> values) {
        StringBuilder groundPredicate = new StringBuilder();
        groundPredicate.append(mutex.predSymbolName);

        // Now iterate over all the parameters of this predicate and replace them with the param/value

        for (Integer idParam : mutex.paramsId) {
            // Get the param from the candidate
            AtomVariable var = mutex.candidateParent.variables.get(idParam);
            
            // Check if it is a param or a value
            boolean isValue = var.isCountedVar;

            if (isValue) {
                // Get the value
                String value = values.get(var.idInAtomCandidate);
                groundPredicate.append("_" + value);
            } else {
                // Get the param
                String param = params.get(var.idInAtomCandidate);
                groundPredicate.append("_" + param);
            }
        }
        return groundPredicate.toString();
    }

    private static ArrayList<String> getPredicateParametersFromParamsValuesMutex(AtomCandidate mutex, ArrayList<String> params, ArrayList<String> values) {
        ArrayList<String> paramsGroundPredicate = new ArrayList<String>();

        // Fill the list of parameters

        for (Integer idParam : mutex.paramsId) {
            // Get the param from the candidate
            AtomVariable var = mutex.candidateParent.variables.get(idParam);
            
            // Check if it is a param or a value
            boolean isValue = var.isCountedVar;

            if (isValue) {
                // Get the value
                String value = values.get(var.idInAtomCandidate);
                paramsGroundPredicate.add(value);
            } else {
                // Get the param
                String param = params.get(var.idInAtomCandidate);
                paramsGroundPredicate.add(param);
            }
        }
        return paramsGroundPredicate;
    }

    private static Integer getPredicateIdFromSASPredicateWithParamsValues(AtomCandidate mutex, ArrayList<String> params, ArrayList<String> values) {
        StringBuilder groundPredicate = new StringBuilder();
        ArrayList<String> paramsGroundPredicate = new ArrayList<String>();

        // Now iterate over all the parameters of this predicate and replace them with the param/value

        for (Integer idParam : mutex.paramsId) {
            // Get the param from the candidate
            AtomVariable var = mutex.candidateParent.variables.get(idParam);
            
            // Check if it is a param or a value
            boolean isValue = var.isCountedVar;

            if (isValue) {
                // Get the value
                String value = values.get(var.idInAtomCandidate);
                paramsGroundPredicate.add(value);
            } else {
                // Get the param
                String param = params.get(var.idInAtomCandidate);
                paramsGroundPredicate.add(param);
            }
        }

        // Get the predicate id
        Integer predicateId = UtilsStructureProblem.getPredicateID(mutex.predSymbolName, paramsGroundPredicate);

        return predicateId;
    }

    /**
     * Return the binary value of the predicate into the clique in SMT format. Create lg2(n) variables with n the number of values in the clique. 
     * The time step is added to all the variables name at the end.
     * For example, if our predicate is in the clique 0 and has the value 2, and there is a total of 5 values (and we are at time step 0):  
     * (assert (and (= Clique_0_bit0__0 false) (= Clique_0_bit1__0 true) (= Clique_0_bit3__0 false)
     * @param CliqueID
     * @param valuePredicateInClique
     * @param totalNumberValuesInClique
     * @param timeStep
     * @return
     */
    public static String getBinaryValueInSMTFormat(int CliqueID, int valuePredicateInClique, int totalNumberValuesInClique, int timeStep) {
        StringBuilder binaryValue = new StringBuilder();
        binaryValue.append("(assert (and ");
        int nbBits = (int) Math.ceil(Math.log(totalNumberValuesInClique) / Math.log(2));
        for (int i = 0; i < nbBits; i++) {
            int value = (int) Math.pow(2, i);
            if ((valuePredicateInClique & value) == value) {
                binaryValue.append("Clique_" + CliqueID + "_bit" + i + "__" + timeStep + " ");
            } else {
                binaryValue.append("(not Clique_" + CliqueID + "_bit" + i + "__" + timeStep + ") ");
            }
        }
        binaryValue.append("))\n");
        return binaryValue.toString();
    }

    /**
     * @param CliqueID
     * @param valuePredicateInClique
     * @param totalNumberValuesInClique
     * @param timeStep
     * @return
     */
    public static ArrayList<Boolean> getBinaryValueOfPredicateInClique(int CliqueID, int totalNumberValuesInClique, int valuePredicateInClique) {
        ArrayList<Boolean> binaryValue = new ArrayList<Boolean>();
        int nbBits = (int) Math.ceil(Math.log(totalNumberValuesInClique) / Math.log(2));
        for (int i = 0; i < nbBits; i++) {
            int value = (int) Math.pow(2, i);
            if ((valuePredicateInClique & value) == value) {
                binaryValue.add(true);
            } else {
                binaryValue.add(false);
            }
        }
        return binaryValue;
    }

    public static String generateFrameAxiomsForPredicatesWithSASPlus(HashMap<Integer, ArrayList<Pair<LiftedFlow, CertifiedPredicate>>> allPredicateWhichHaveBeenChangedForThisTimeStep, int timeStep, HashSet<CertifiedPredicate> pseudoFactsToDefine, HashSet<String> groundFactsToDefine, HashSet<String> cliqueBitsToDefine) {
        StringBuilder frameAxioms = new StringBuilder();

        // If some predicate are not in the SAS groups, we need to add them to the frame axioms in the classical way
        HashMap<Integer, ArrayList<Pair<LiftedFlow, CertifiedPredicate>>> allPosPredicateWhichHaveBeenChangedForThisTimeStep = new HashMap<Integer, ArrayList<Pair<LiftedFlow, CertifiedPredicate>>>();
        HashMap<Integer, ArrayList<Pair<LiftedFlow, CertifiedPredicate>>> allNegPredicateWhichHaveBeenChangedForThisTimeStep = new HashMap<Integer, ArrayList<Pair<LiftedFlow, CertifiedPredicate>>>();

        HashSet<Integer> cliquesUpdated = new HashSet<Integer>();

        // Iterate over all predicates which may have been changed (key is the predicate id)
        for (Integer predicateId : allPredicateWhichHaveBeenChangedForThisTimeStep.keySet()) {

            // Get the list of all the flows and the corresponding effect which may have changed this predicate
            ArrayList<Pair<LiftedFlow, CertifiedPredicate>> allFlowsAndEffWhichMayHaveChangedThisPredicate = allPredicateWhichHaveBeenChangedForThisTimeStep.get(predicateId);

            // Get all the SAS groups of this predicate
            SASPredicate predicate = UtilsStructureProblem.predicatesSAS[predicateId];

            if (predicate.cliques.size() == 0) {
                System.out.println("Error: the predicate " + predicate.fullName + " has no cliques. NEED TO IMPLEMENT THIS CASE !");
                // System.exit(0);
                // Iterate over all flows and effects which may have changed this predicate

                for (Pair<LiftedFlow, CertifiedPredicate> flowWhichMayHaveChangedPredWithEff : allFlowsAndEffWhichMayHaveChangedThisPredicate) {
                    LiftedFlow flow = flowWhichMayHaveChangedPredWithEff.getLeft();
                    CertifiedPredicate effect = flowWhichMayHaveChangedPredWithEff.getRight();
                    if (effect.isPositive) {
                        if (!allPosPredicateWhichHaveBeenChangedForThisTimeStep.containsKey(predicateId)) {
                            allPosPredicateWhichHaveBeenChangedForThisTimeStep.put(predicateId, new ArrayList<Pair<LiftedFlow, CertifiedPredicate>>());
                        }
                        allPosPredicateWhichHaveBeenChangedForThisTimeStep.get(predicateId).add(flowWhichMayHaveChangedPredWithEff);
                    } else {
                        if (!allNegPredicateWhichHaveBeenChangedForThisTimeStep.containsKey(predicateId)) {
                            allNegPredicateWhichHaveBeenChangedForThisTimeStep.put(predicateId, new ArrayList<Pair<LiftedFlow, CertifiedPredicate>>());
                        }
                        allNegPredicateWhichHaveBeenChangedForThisTimeStep.get(predicateId).add(flowWhichMayHaveChangedPredWithEff);
                    }
                }
                // Go to the next predicate
                continue;
            }


            if (predicate.cliques.size() > 1) {
                int debug = 0;
            }

            // Iterate over all the cliques of this predicate
            for (int cliqueIdx = 0; cliqueIdx < predicate.cliques.size(); cliqueIdx++) {

                StringBuilder frameAxiomsOneClique = new StringBuilder();

                // So here, we consider that the predicate is only in one clique
                Clique clique = predicate.cliques.get(cliqueIdx);

                // Check if we have already generated the frame axioms for this clique
                if (cliquesUpdated.contains(clique.id)) {
                    continue;
                }

                StringBuilder allFlowsAreFalse = new StringBuilder("(and ");
                StringBuilder actionTrueAndUnificationToPreventPredicateFromBeingChanged = new StringBuilder();


                // The rule of the frame axioms for a predicate P which is in a clique C is (for all actions a which may change P):
                // (OR (AND not a for all a) (OR A and specific grounding of the pseudo facts which prevent P from being changed) => P next step = P last defined step

                // Iterate over all flows which may have changed this predicate
                for (Pair<LiftedFlow, CertifiedPredicate> flowsWhichMayHaveChangedPredWithEff : allFlowsAndEffWhichMayHaveChangedThisPredicate) {
                    LiftedFlow flow = flowsWhichMayHaveChangedPredWithEff.getLeft();
                    CertifiedPredicate effect = flowsWhichMayHaveChangedPredWithEff.getRight();
                    allFlowsAreFalse.append("(not " + flow.getUniqueName() + ") ");

                    // Add the effect as well 
                    // pseudoFactsToDefine.add(effect);

                    // Write the effect
                    // frameAxioms.append("(assert (=> " + flow.getUniqueName() + " " + effect.toSmt(timeStep) + "))\n");


                    if (clique.params.size() > 0) {
                        actionTrueAndUnificationToPreventPredicateFromBeingChanged.append("(and " + flow.getUniqueName() + " ");
                    }
                    
                    // Now see how this effect should be grounded to prevent the predicate from being changed
                    
                    // Confirm that the LFG of this clique has the same predicate name as the predicate
                    // if (!clique.LFG.predicateName.equals(predicate.)) {
                    //     System.out.println("Error: the predicate " + predicate.fullName + " is in the clique " + clique.id + " but the LFG of this clique has the predicate name " + clique.lfg.predicateName);
                    //     System.exit(0);
                    // }
                    Candidate LFGParentOfClique = clique.LFG;

                    // Iterate over all mutexGroup of this LFG to get the one with the same predicate name as the predicateb

                    boolean foundMutexGroup = false;

                    for (AtomCandidate mutexGroup : LFGParentOfClique.mutexGroup) {
                        if (!mutexGroup.predSymbolName.equals(predicate.predicateName)) {
                            continue;
                        }

                        foundMutexGroup = true;
                        // Iterate over all its argument until we have a param and check which params value is taken with the clique 
                        for (int paramIdx = 0; paramIdx < mutexGroup.paramsId.size(); paramIdx++) {
                            Integer paramId = mutexGroup.paramsId.get(paramIdx);
                            AtomVariable var = LFGParentOfClique.variables.get(paramId);
                            if (var.isCountedVar) {
                                continue;
                            }
                            // Get the value of this param in the clique
                            String valueInClique = clique.params.get(var.idInAtomCandidate);

                            // We must indicate that the scope of the certified predicate must be different from the value in clique
                            // actionTrueAndUnificationToPreventPredicateFromBeingChanged.append("(not (= " + effect.scope.get(paramIdx).getUniqueName() + " " + valueInClique + ")) ");
                            if (effect.scope.get(paramIdx).isConstant()) {
                                if (effect.scope.get(paramIdx).getUniqueName().equals(valueInClique)) {
                                    actionTrueAndUnificationToPreventPredicateFromBeingChanged.append("false ");
                                } else {
                                    actionTrueAndUnificationToPreventPredicateFromBeingChanged.append("true ");
                                }
                            } else {
                                actionTrueAndUnificationToPreventPredicateFromBeingChanged.append("(not " + effect.scope.get(paramIdx).getUniqueName() + "__" + valueInClique + ") ");
                            }
                            
                        }
                    }

                    if (clique.params.size() > 0) {
                        actionTrueAndUnificationToPreventPredicateFromBeingChanged.append(") ");
                    }
                    

                    int b = 0;
                }

                allFlowsAreFalse.append(") ");

                StringBuilder newValueEachBitOfClique = new StringBuilder("(and ");

                // Get the number of bits used to represent this clique
                int nbBitsToRepresentClique = clique.getNbBits();
                // Get the last time this clique was defined
                int lastTimeCliqueWasDefined = clique.getLastTimeCliqueWasDefined();

                // Set the rule to indicate that the bit has not changed 
                for (int i = 0; i < nbBitsToRepresentClique; i++) {
                    String bitName = "Clique_" + clique.id + "_bit" + i + "__" + timeStep;
                    String bitNameLastTimeCliqueWasDefined = "Clique_" + clique.id + "_bit" + i + "__" + lastTimeCliqueWasDefined;

                    newValueEachBitOfClique.append("(= " + bitName + " " + bitNameLastTimeCliqueWasDefined + ") ");
                    // groundFactsToDefine.add(bitName);
                    cliqueBitsToDefine.add(bitName);
                }
                newValueEachBitOfClique.append(")");

                frameAxiomsOneClique.append("(assert (=> (or " + allFlowsAreFalse.toString() + actionTrueAndUnificationToPreventPredicateFromBeingChanged.toString() + ") " + newValueEachBitOfClique.toString() + "))\n");

                System.out.println("Frame axioms on predicate: " + predicate.fullName);
                System.out.println(frameAxiomsOneClique.toString());

                // Update the last time this clique was defined
                clique.setLastTimeCliqueWasDefined(timeStep);

                // Indicate that this clique has been updated
                cliquesUpdated.add(clique.id);

                // Update the frame axioms
                frameAxioms.append("; update clique: " + clique.toString() + "\n");
                frameAxioms.append(frameAxiomsOneClique.toString());
                int a = 0;
            }
        }

        if (allPosPredicateWhichHaveBeenChangedForThisTimeStep.size() > 0 || allNegPredicateWhichHaveBeenChangedForThisTimeStep.size() > 0) {
            String classicalFrameAxioms = generateFrameAxiomsForPredicatesWithoutSASPlus(allPosPredicateWhichHaveBeenChangedForThisTimeStep, allNegPredicateWhichHaveBeenChangedForThisTimeStep, timeStep, pseudoFactsToDefine, groundFactsToDefine);
            // Append the classical frame axioms
            frameAxioms.append(classicalFrameAxioms);
        }
       
       return frameAxioms.toString();
    }


    public static String generateFrameAxiomsForPredicatesWithoutSASPlus(HashMap<Integer, ArrayList<Pair<LiftedFlow, CertifiedPredicate>>> allPosPredicateWhichHaveBeenChangedForThisTimeStep, HashMap<Integer, ArrayList<Pair<LiftedFlow, CertifiedPredicate>>> allNegPredicateWhichHaveBeenChangedForThisTimeStep, int timeStep, HashSet<CertifiedPredicate> pseudoFactsToDefine, HashSet<String> groundFactsToDefine) {
        StringBuilder frameAxioms = new StringBuilder();

        HashSet<Integer> allPredicatesToUpdate = new HashSet<Integer>();

        // Iterate over all positive predicates which may have been changed (key is the predicate id)
        for (Integer predicateId : allPosPredicateWhichHaveBeenChangedForThisTimeStep.keySet()) {

            // Get the predicate object
            SASPredicate predicate = UtilsStructureProblem.predicatesSAS[predicateId];

            // Get the last time that this predicate was defined
            int lastTimePredicateWasDefined = predicate.getLastTimePredicateWasDefined();

            String predicateLastTimeDefined = predicate.getFullName() + "__" + lastTimePredicateWasDefined;
            String predicateThisTimeDefined = predicate.getFullName() + "__" + timeStep;

            // Add the predicate to the list of ground facts to define
            groundFactsToDefine.add(predicateThisTimeDefined);

            // Implement the rule 14 of the lilotane paper: if a predicate has been changed, then there must have been an action which has changed it
            frameAxioms.append("(assert (=> (and (not " + predicateLastTimeDefined + ") " + predicateThisTimeDefined + ") (or ");
            for (Pair<LiftedFlow, CertifiedPredicate> flowsWhichMayHaveChangedPredWithEff : allPosPredicateWhichHaveBeenChangedForThisTimeStep.get(predicateId)) {
                frameAxioms.append(flowsWhichMayHaveChangedPredWithEff.getLeft().getUniqueName() + " ");
            }
            frameAxioms.append(")))\n");

            // Now, do the rule 15: if a fact is changed and some action is true, then some set of substition must be active which unify the fact with the action
            for (Pair<LiftedFlow, CertifiedPredicate> flowsWhichMayHaveChangedPredWithEff : allPosPredicateWhichHaveBeenChangedForThisTimeStep.get(predicateId)) {
                frameAxioms.append("(assert (=> (and (not " + predicateLastTimeDefined + ") " + predicateThisTimeDefined + " " + flowsWhichMayHaveChangedPredWithEff.getLeft().getUniqueName() + ") (and ");
                CertifiedPredicate eff = flowsWhichMayHaveChangedPredWithEff.getRight();
                boolean atLeastOne = false;
                for (int i = 0; i < eff.scope.size(); i++) {
                    if (eff.scope.get(i).isConstant()) {
                        if (!eff.scope.get(i).getUniqueName().equals(predicate.getParams().get(i))) {
                            atLeastOne = true;
                            frameAxioms.append(eff.scope.get(i).getUniqueName() + "__" + predicate.getParams().get(i) + " ");
                        }
                    } else {
                        atLeastOne = true;
                        frameAxioms.append(eff.scope.get(i).getUniqueName() + "__" + predicate.getParams().get(i) + " ");
                    }
                }
                if (!atLeastOne) {
                    frameAxioms.append("true ");
                }
                frameAxioms.append(")))\n");
                
            }

            allPredicatesToUpdate.add(predicateId);

            // Here, we have indicated all the way where this predicate can become true if it was false before. But, if there is no action which may change this predicate from true to false,
            // then we must indicate that this predicate is true if it was true before
            if (!allNegPredicateWhichHaveBeenChangedForThisTimeStep.containsKey(predicateId)) {
                frameAxioms.append("(assert (=> " +  predicateLastTimeDefined + " " + predicateThisTimeDefined + "))\n");
            }
        }

        // Do the same for the negative predicates
        for (Integer predicateId : allNegPredicateWhichHaveBeenChangedForThisTimeStep.keySet()) {

            // Get the predicate object
            SASPredicate predicate = UtilsStructureProblem.predicatesSAS[predicateId];

            // Get the last time that this predicate was defined
            int lastTimePredicateWasDefined = predicate.getLastTimePredicateWasDefined();

            String predicateLastTimeDefined = predicate.getFullName() + "__" + lastTimePredicateWasDefined;
            String predicateThisTimeDefined = predicate.getFullName() + "__" + timeStep;

            // Add the predicate to the list of ground facts to define
            groundFactsToDefine.add(predicateThisTimeDefined);


            // Implement the rule 14 of the lilotane paper: if a predicate has been changed, then there must have been an action which has changed it
            frameAxioms.append("(assert (=> (and " + predicateLastTimeDefined + " (not " + predicateThisTimeDefined + ")) (or ");
            for (Pair<LiftedFlow, CertifiedPredicate> flowsWhichMayHaveChangedPredWithEff : allNegPredicateWhichHaveBeenChangedForThisTimeStep.get(predicateId)) {
                frameAxioms.append(flowsWhichMayHaveChangedPredWithEff.getLeft().getUniqueName() + " ");
            }
            frameAxioms.append(")))\n");

            // Now, do the rule 15: if a fact is changed and some action is true, then some set of substition must be active which unify the fact with the action
            for (Pair<LiftedFlow, CertifiedPredicate> flowsWhichMayHaveChangedPredWithEff : allNegPredicateWhichHaveBeenChangedForThisTimeStep.get(predicateId)) {
                frameAxioms.append("(assert (=> (and " + predicateLastTimeDefined + " (not " + predicateThisTimeDefined + ") " + flowsWhichMayHaveChangedPredWithEff.getLeft().getUniqueName() + ") (and ");
                CertifiedPredicate eff = flowsWhichMayHaveChangedPredWithEff.getRight();
                boolean atLeastOne = false;
                for (int i = 0; i < eff.scope.size(); i++) {
                    if (eff.scope.get(i).isConstant()) {
                        if (!eff.scope.get(i).getUniqueName().equals(predicate.getParams().get(i))) {
                            atLeastOne = true;
                            frameAxioms.append(eff.scope.get(i).getUniqueName() + "__" + predicate.getParams().get(i) + " ");
                        }
                    } else {
                        atLeastOne = true;
                        frameAxioms.append(eff.scope.get(i).getUniqueName() + "__" + predicate.getParams().get(i) + " ");
                    }
                }
                if (!atLeastOne) {
                    frameAxioms.append("true ");
                }
                frameAxioms.append(")))\n");
                
            }

            allPredicatesToUpdate.add(predicateId);

            // Here, we have indicated all the way where this predicate can become false if it was true before. But, if there is no action which may change this predicate from false to true,
            // then we must indicate that this predicate is false if it was false before
            if (!allPosPredicateWhichHaveBeenChangedForThisTimeStep.containsKey(predicateId)) {
                frameAxioms.append("(assert (=> (not " +  predicateLastTimeDefined + ") (not " + predicateThisTimeDefined + ")))\n");
            }
        }



        // At the end, update the last time that each predicate was defined
        for (Integer predicateId : allPredicatesToUpdate) {
            SASPredicate predicate = UtilsStructureProblem.predicatesSAS[predicateId];
            predicate.setLastTimePredicateWasDefined(timeStep);
        }


        return frameAxioms.toString();
    }
}

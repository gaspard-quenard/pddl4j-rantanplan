package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

import java.util.ArrayList;
import java.util.HashSet;

import org.apache.commons.lang3.tuple.Pair;

public class EffActionsAndFrameAxioms {
    
    String predicateName;
    HashSet<DefinerPredEffAction> definerPredPosEffActions;
    HashSet<DefinerPredEffAction> definerPredNegEffActions;

    public EffActionsAndFrameAxioms(String predicateName) {
        this.predicateName = predicateName;
        this.definerPredPosEffActions = new HashSet<DefinerPredEffAction>();
        this.definerPredNegEffActions = new HashSet<DefinerPredEffAction>();
    }

    public void addDefinerPredPosEffAction(DefinerPredEffAction definerPredEffAction) {
        this.definerPredPosEffActions.add(definerPredEffAction);
    }

    public void addDefinerPredNegEffAction(DefinerPredEffAction definerPredEffAction) {
        this.definerPredNegEffActions.add(definerPredEffAction);
    }

    public void addPosEffectAction(String flowName, CertifiedPredicate pred) {
        this.definerPredPosEffActions.add(new DefinerPredEffAction(flowName, pred.scope, pred));
    }

    public void addNegEffectAction(String flowName, CertifiedPredicate pred) {
        this.definerPredNegEffActions.add(new DefinerPredEffAction(flowName, pred.scope, pred));
    }


    /**
     * Write the SMT-LIB2 file for the frame axioms and the effect actions (based on the rule 14 and 15 from the lilotane paper)
     * @return
     */
    public String toSmt(int currentTimeStep, HashSet<CertifiedPredicate> pseudoFactsToDefine, HashSet<String> groundFactsToDefine) {
        StringBuilder sb = new StringBuilder();

        HashSet<Pair<String, ArrayList<String>>> allGroundPredicatesToUpdate = new HashSet<Pair<String, ArrayList<String>>>();

        HashSet<Integer> cliquesAlreadyDefined = new HashSet<Integer>();



        // First, fully define each predicate
        // HashSet<String> scopesAlreadyDefined = new HashSet<String>();
        // for (DefinerPredEffAction definerPredEffAction : this.definerPredPosEffActions) {

        //     // See if we have already defined these scopes
        //     StringBuilder scopesKey = new StringBuilder();
        //     for (ScopeVariable param : definerPredEffAction.params) {
        //         scopesKey.append(param.getUniqueName());
        //     }
            
        //     // Check if the predicate is already defined
        //     if (scopesAlreadyDefined.contains(scopesKey.toString())) {
        //         continue;
        //     }

        //     // Generate the rule 13 for this predicate
        //     String definePseudoFact = UtilsStructureProblem.generateRuleConversionPseudoFactToGroundFact(predicateName, definerPredEffAction.params, currentTimeStep, false);
        //     sb.append(definePseudoFact);

        //     scopesAlreadyDefined.add(scopesKey.toString());
        // }


        // for (DefinerPredEffAction definerPredEffAction : this.definerPredNegEffActions) {

        //     // See if we have already defined these scopes
        //     StringBuilder scopesKey = new StringBuilder();
        //     for (ScopeVariable param : definerPredEffAction.params) {
        //         scopesKey.append(param.getUniqueName());
        //     }
            
        //     // Check if the predicate is already defined
        //     if (scopesAlreadyDefined.contains(scopesKey.toString())) {
        //         continue;
        //     }

        //     // Generate the rule 13 for this predicate
        //     String definePseudoFact = UtilsStructureProblem.generateRuleConversionPseudoFactToGroundFact(predicateName, definerPredEffAction.params, currentTimeStep, false);
        //     sb.append(definePseudoFact);

        //     scopesAlreadyDefined.add(scopesKey.toString());
        // }

        for (DefinerPredEffAction definerPredEffAction : this.definerPredPosEffActions) {

            if (definerPredEffAction.certPred.isGroundFact()) {
                groundFactsToDefine.add(definerPredEffAction.certPred.toSmt(currentTimeStep));
                continue;
            }

            // Add this pseudo fact to the list of pseudo facts to define (only if it is not already in it)
            boolean alreadyIn = false;
            for (CertifiedPredicate certPredAlreadyDefined : pseudoFactsToDefine) {
                if (certPredAlreadyDefined.isEqualOrOppositeTo(definerPredEffAction.certPred)) {
                    alreadyIn = true;
                    break;
                }   
            }
            if (!alreadyIn) {
                pseudoFactsToDefine.add(definerPredEffAction.certPred);
            }
        }
        for (DefinerPredEffAction definerPredEffAction : this.definerPredNegEffActions) {

            if (definerPredEffAction.flowName.equals("FLOW_drive_77") || definerPredEffAction.flowName.equals("FLOW_drive_96")) {
                int a = 0;
            }

            if (definerPredEffAction.certPred.isGroundFact()) {
                groundFactsToDefine.add(definerPredEffAction.certPred.toSmt(currentTimeStep));
                continue;
            }
            
            // Add this pseudo fact to the list of pseudo facts to define (only if it is not already in it)
            boolean alreadyIn = false;
            for (CertifiedPredicate certPredAlreadyDefined : pseudoFactsToDefine) {
                if (certPredAlreadyDefined.isEqualOrOppositeTo(definerPredEffAction.certPred)) {
                    alreadyIn = true;
                    break;
                }   
            }
            if (!alreadyIn) {
                pseudoFactsToDefine.add(definerPredEffAction.certPred);
            }
        }


        // First, add all the scope values of all the definer predicates
        ArrayList<HashSet<String>> allObjectsForAllParametersFrameAxiomsPos = new ArrayList<HashSet<String>>();
        ArrayList<HashSet<String>> allObjectsForAllParametersFrameAxiomsNeg = new ArrayList<HashSet<String>>();

        for (DefinerPredEffAction definerPredEffAction : this.definerPredPosEffActions) {

            // First, write the effect of the action
            sb.append("(assert (=> " + definerPredEffAction.flowName +  " " + predicateName );
            for (ScopeVariable param : definerPredEffAction.params) {
                sb.append("_" + param.getUniqueName());
            }
            sb.append("__" + currentTimeStep + "))\n");

            for (ScopeVariable param : definerPredEffAction.params) {

                // Create the set if not exist
                if (allObjectsForAllParametersFrameAxiomsPos.size() < definerPredEffAction.params.size()) {
                    allObjectsForAllParametersFrameAxiomsPos.add(new HashSet<String>());
                }

                // Add all the scope values into the set
                allObjectsForAllParametersFrameAxiomsPos.get(definerPredEffAction.params.indexOf(param)).addAll(param.getPossibleValueVariable());
            }
        }

        // Do the same for the negative effect
        for (DefinerPredEffAction definerPredEffAction : this.definerPredNegEffActions) {

            // First, write the effect of the action
            sb.append("(assert (=> " + definerPredEffAction.flowName +  " (not " + predicateName );
            for (ScopeVariable param : definerPredEffAction.params) {
                sb.append("_" + param.getUniqueName());
            }
            sb.append("__" + currentTimeStep + ")))\n");

            for (ScopeVariable param : definerPredEffAction.params) {

                // Create the set if not exist
                if (allObjectsForAllParametersFrameAxiomsNeg.size() < definerPredEffAction.params.size()) {
                    allObjectsForAllParametersFrameAxiomsNeg.add(new HashSet<String>());
                }

                // Add all the scope values into the set
                allObjectsForAllParametersFrameAxiomsNeg.get(definerPredEffAction.params.indexOf(param)).addAll(param.getPossibleValueVariable());
            }
        }

        // Now generate all the possible combinaisons to get all the predicate which may have changed here
        ArrayList<ArrayList<String>> allPossibleCombinationsPos = new ArrayList<ArrayList<String>>();
        for (HashSet<String> allObjectsForParamI : allObjectsForAllParametersFrameAxiomsPos) {
            ArrayList<ArrayList<String>> newAllPossibleCombinations = new ArrayList<ArrayList<String>>();
            for (String object : allObjectsForParamI) {
                if (allPossibleCombinationsPos.isEmpty()) {
                    ArrayList<String> newCombination = new ArrayList<String>();
                    newCombination.add(object);
                    newAllPossibleCombinations.add(newCombination);
                } else {
                    for (ArrayList<String> combination : allPossibleCombinationsPos) {
                        ArrayList<String> newCombination = new ArrayList<String>();
                        newCombination.addAll(combination);
                        newCombination.add(object);
                        newAllPossibleCombinations.add(newCombination);
                    }
                }
            }
            allPossibleCombinationsPos = newAllPossibleCombinations;
        }

        // Do the same for the negative effect
        ArrayList<ArrayList<String>> allPossibleCombinationsNeg = new ArrayList<ArrayList<String>>();
        for (HashSet<String> allObjectsForParamI : allObjectsForAllParametersFrameAxiomsNeg) {
            ArrayList<ArrayList<String>> newAllPossibleCombinations = new ArrayList<ArrayList<String>>();
            for (String object : allObjectsForParamI) {
                if (allPossibleCombinationsNeg.isEmpty()) {
                    ArrayList<String> newCombination = new ArrayList<String>();
                    newCombination.add(object);
                    newAllPossibleCombinations.add(newCombination);
                } else {
                    for (ArrayList<String> combination : allPossibleCombinationsNeg) {
                        ArrayList<String> newCombination = new ArrayList<String>();
                        newCombination.addAll(combination);
                        newCombination.add(object);
                        newAllPossibleCombinations.add(newCombination);
                    }
                }
            }
            allPossibleCombinationsNeg = newAllPossibleCombinations;
        }

        // We need to do the frame axioms for all the predicate in the allPossibleCombinations
        for (ArrayList<String> groundPredicateParam : allPossibleCombinationsPos) {

            // if (LiftedTreePathConfig.useSASPlusEncoding) {
            //     //  Check if this ground predicate is in a LFG
            //     boolean isInLFG = false;
            //     Integer idPred = UtilsStructureProblem.getPredicateID(predicateName, groundPredicateParam);
            //     SASPredicate sasPredicate = UtilsStructureProblem.predicatesSAS[idPred];
            //     if (sasPredicate == null) {
            //         // The predicate is not in a LFG
            //         isInLFG = false;
            //         System.out.println("Should handle the case where the predicate is not in a LFG !");
            //         System.exit(0);
            //     }

            //     // Update the LFG
            //     int a = 0;
            // }

            String groundPredicate;
            if (groundPredicateParam.isEmpty()) {
                groundPredicate = predicateName;
            } else {
                groundPredicate = predicateName + "_" + String.join("_", groundPredicateParam);
            }

            HashSet<DefinerPredEffAction> allFlowsWhichMayHaveChangedThisPredicate = new HashSet<DefinerPredEffAction>();
            // Add all the flows which may have changed this predicate. We need to check if the scope value of each parameter of the definer predicate contains the parameter of the ground predicate
            for (DefinerPredEffAction d : this.definerPredPosEffActions) {
                boolean allParamsMatch = true;
                for (int i = 0; i < d.params.size(); i++) {
                    if (!d.params.get(i).getPossibleValueVariable().contains(groundPredicateParam.get(i))) {
                        allParamsMatch = false;
                        break;
                    }
                }
                if (allParamsMatch) {
                    allFlowsWhichMayHaveChangedThisPredicate.add(d);
                }
            }
            
            // Add the ground predicate to the new vars to define (only for the current time step)
            groundFactsToDefine.add(groundPredicate + "__" + currentTimeStep);
            allGroundPredicatesToUpdate.add(Pair.of(predicateName, groundPredicateParam));

            // Get the last time this predicate was defined
            int lastTimePredicateDefined = UtilsStructureProblem.getLastTimePredicateDefined(predicateName, groundPredicateParam);

            // Now we can implement the frame axiom (if a predicate change, then an action which may have changed this predicate must have been executed)
            // Rule 14 from the lilotane paper
            if (allFlowsWhichMayHaveChangedThisPredicate.size() > 0) {
                sb.append("(assert (=> (and (not " + groundPredicate + "__" + lastTimePredicateDefined + ") " + groundPredicate + "__" + currentTimeStep + ") (or ");
                for (DefinerPredEffAction flow : allFlowsWhichMayHaveChangedThisPredicate) {
                    sb.append(flow.flowName + " ");
                }
                sb.append(")))\n");
            }


            // Now, make the rule 15, if a fact is changed and some action is true, then some set of substition must be active which unify the fact with the action
            // TODO here we only consider that only one predicate of an action can be changed. We need to consider the case where multiple predicates are changed
            for (DefinerPredEffAction definerPred : allFlowsWhichMayHaveChangedThisPredicate) {
                if (definerPred.certPred.isGroundFact()) {
                    continue;
                }
                sb.append("(assert (=> (and " + definerPred.flowName + " (not " + groundPredicate + "__" + lastTimePredicateDefined + ") " + groundPredicate + "__" + currentTimeStep + ") (and ");
                for (int i = 0; i < definerPred.params.size(); i++) {
                    if (!definerPred.params.get(i).isConstant()) {
                        sb.append(definerPred.params.get(i).getUniqueName() + "__" + groundPredicateParam.get(i) + " ");
                    }
                }
                sb.append(")))\n");
            }

            // Check if the negative combainaison contains this
            if (!allPossibleCombinationsNeg.contains(groundPredicateParam)) {
                // It means there is no action which make this action becomes false if it was true at previous time step. 
                // So, if this predicate was true, then it must keep being true
                sb.append("(assert (=> " + groundPredicate + "__" + lastTimePredicateDefined + " " + groundPredicate + "__" + currentTimeStep + "))\n");
            }
        }

        // Do the same for the negative effect
        for (ArrayList<String> groundPredicateParam : allPossibleCombinationsNeg) {

            String groundPredicate;
            if (groundPredicateParam.isEmpty()) {
                groundPredicate = predicateName;
            } else {
                groundPredicate = predicateName + "_" + String.join("_", groundPredicateParam);
            }

            HashSet<DefinerPredEffAction> allFlowsWhichMayHaveChangedThisPredicate = new HashSet<DefinerPredEffAction>();
            // Add all the flows which may have changed this predicate. We need to check if the scope value of each parameter of the definer predicate contains the parameter of the ground predicate
            for (DefinerPredEffAction d : this.definerPredNegEffActions) {
                boolean allParamsMatch = true;
                for (int i = 0; i < d.params.size(); i++) {
                    if (!d.params.get(i).getPossibleValueVariable().contains(groundPredicateParam.get(i))) {
                        allParamsMatch = false;
                        break;
                    }
                }
                if (allParamsMatch) {
                    allFlowsWhichMayHaveChangedThisPredicate.add(d);
                }
            }
            
            // Add the ground predicate to the new vars to define (only for the current time step)
            groundFactsToDefine.add(groundPredicate + "__" + currentTimeStep);
            allGroundPredicatesToUpdate.add(Pair.of(predicateName, groundPredicateParam));

            // Get the last time this predicate was defined
            int lastTimePredicateDefined = UtilsStructureProblem.getLastTimePredicateDefined(predicateName, groundPredicateParam);

            // Now we can implement the frame axiom (if a predicate change, then an action which may have changed this predicate must have been executed)
            // Rule 14 from the lilotane paper
            if (allFlowsWhichMayHaveChangedThisPredicate.size() > 0) {
                sb.append("(assert (=> (and " + groundPredicate + "__" + lastTimePredicateDefined + " (not " + groundPredicate + "__" + currentTimeStep + ")) (or ");
                for (DefinerPredEffAction flow : allFlowsWhichMayHaveChangedThisPredicate) {
                    sb.append(flow.flowName + " ");
                }
                sb.append(")))\n");
            }


            // Now, make the rule 15, if a fact is changed and some action is true, then some set of substition must be active which unify the fact with the action
            // TODO here we only consider that only one predicate of an action can be changed. We need to consider the case where multiple predicates are changed
            for (DefinerPredEffAction definerPred : allFlowsWhichMayHaveChangedThisPredicate) {
                if (definerPred.certPred.isGroundFact()) {
                    continue;
                }
                sb.append("(assert (=> (and " + definerPred.flowName + " " + groundPredicate + "__" + lastTimePredicateDefined + " (not " + groundPredicate + "__" + currentTimeStep + ")) (and ");
                for (int i = 0; i < definerPred.params.size(); i++) {
                    if (!definerPred.params.get(i).isConstant()) {
                        sb.append(definerPred.params.get(i).getUniqueName() + "__" + groundPredicateParam.get(i) + " ");
                    }
                }
                sb.append(")))\n");
            }


            // Check if the negative combainaison contains this
            if (!allPossibleCombinationsPos.contains(groundPredicateParam)) {
                // It means there is no action which make this action becomes true if it was false at previous time step. 
                // So, if this predicate was false, then it must keep being false
                sb.append("(assert (=> (not " + groundPredicate + "__" + lastTimePredicateDefined + ") (not " + groundPredicate + "__" + currentTimeStep + ")))\n");
            }
        }


        // Update the last time the predicate was defined
        for (Pair<String, ArrayList<String>> predicate : allGroundPredicatesToUpdate) {
            String predicateName = predicate.getLeft();
            ArrayList<String> groundPredicateParam = predicate.getRight();
            UtilsStructureProblem.updateLastTimePredicateDefined(predicateName, groundPredicateParam, currentTimeStep);
        }



        return sb.toString();
    }


    /**
     * Generate all the possible combinations of the parameters of the definer predicate. For example, if the definer predicate is (definer-pred ?x ?y ?z) and the possible objects for each parameter are:
     * ?x: [obj1, obj2]
     * ?y: [obj3, obj4]
     * ?z: [obj5, obj6]
     * Then, the possible combinations are:
     * [obj1, obj3, obj5]
     * [obj1, obj3, obj6]
     * [obj1, obj4, obj5]
     * [obj1, obj4, obj6]
     * [obj2, obj3, obj5]
     * [obj2, obj3, obj6]
     * [obj2, obj4, obj5]
     * [obj2, obj4, obj6]
     * 
     * @return
     */
    // private ArrayList<ArrayList<String>> generateAllpossibleCombinations() {
    //     ArrayList<ArrayList<String>> allPossibleCombinations = new ArrayList<ArrayList<String>>();
    //     for (int i = 0; i < this.definerPredicate.typesParamPredicate.size(); i++) {
    //         ArrayList<String> possibleObjectsForParam = this.definerPredicate.allObjectsPossibleForEachParams.get(i);
    //         ArrayList<ArrayList<String>> newAllPossibleCombinations = new ArrayList<ArrayList<String>>();
    //         for (String object : possibleObjectsForParam) {
    //             if (allPossibleCombinations.isEmpty()) {
    //                 ArrayList<String> newCombination = new ArrayList<String>();
    //                 newCombination.add(object);
    //                 newAllPossibleCombinations.add(newCombination);
    //             } else {
    //                 for (ArrayList<String> combination : allPossibleCombinations) {
    //                     ArrayList<String> newCombination = new ArrayList<String>(combination);
    //                     newCombination.add(object);
    //                     newAllPossibleCombinations.add(newCombination);
    //                 }
    //             }
    //         }
    //         allPossibleCombinations = newAllPossibleCombinations;
    //     }

    //     return allPossibleCombinations;
    // }
}

class DefinerPredEffAction {
    String flowName;
    ArrayList<ScopeVariable> params;
    CertifiedPredicate certPred;

    public DefinerPredEffAction(String flowName, ArrayList<ScopeVariable> params, CertifiedPredicate certPred) {
        this.flowName = flowName;
        this.params = params;
        this.certPred = certPred;
    }
}

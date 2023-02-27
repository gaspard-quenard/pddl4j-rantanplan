package fr.uga.pddl4j.planners.liftedtreepath_smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Vector;

import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.ParsedMethod;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.SAS_Plus.AtomCandidate;
import fr.uga.pddl4j.parser.SAS_Plus.AtomVariable;
import fr.uga.pddl4j.parser.SAS_Plus.Candidate;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;

public class LiftedFlow {

    static int numberLiftedFlow = 0;

    public int uniqueId;
    private Method method = null;
    private String methodName = null;
    private ArrayList<String> macroAction = null;

    boolean isBlankAction = false;

    LiftedFlow parentFlow = null;
    private Integer parentId; // ID of task for method, ID of method for action
    HashSet<LiftedFlow> nextsFlow;
    HashSet<LiftedFlow> previousesFlow;

    HashSet<CertifiedPredicate> preconditionsHerited;

    Expression<String> preconditions;
    Expression<String> effects;
    ArrayList<Expression<String>> preconditions2;
    ArrayList<Expression<String>> effects2;

    private ArrayList<ScopeVariable> scopeMethod;
    private ArrayList<ArrayList<ScopeVariable>> scopeMacroAction;

    HashSet<CertifiedPredicate> inputCertifiedPredicates;
    HashSet<CertifiedPredicate> outputCertifiedPredicates;
    HashSet<CertifiedPredicate> preconditionPredicates;

    HashSet<LiftedFlow> rootsNodesWhichCanLedToThisFlow;

    Map<CertifiedPredicate, SolverPrecondition> preconditionSolver;

    boolean isPrimitiveFlow;
    int numberChildrenPrimitiveFlow;

    public LiftedFlow(String methodName, LiftedFlow parentFlow, Integer parentTaskId,
            ArrayList<ScopeVariable> methodScope, Map<String, ParsedMethod> methodNameToObject,
            boolean isFirstChildOfMethod) {
        this.methodName = methodName;
        this.parentFlow = parentFlow;
        this.parentId = parentTaskId;
        this.scopeMethod = methodScope;
        isPrimitiveFlow = false;
        this.numberChildrenPrimitiveFlow = 0;

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.rootsNodesWhichCanLedToThisFlow = new HashSet<LiftedFlow>();

        this.preconditionsHerited = new HashSet<CertifiedPredicate>();
        // If we are the first child of a method, we must inherit its preconditions
        if (isFirstChildOfMethod) {
            inheritPreconditionsFromParent(parentFlow, methodNameToObject);
        }

        this.uniqueId = LiftedFlow.numberLiftedFlow;
        LiftedFlow.numberLiftedFlow++;
    }

    public LiftedFlow(ArrayList<String> macroAction, LiftedFlow parentFlow,
            ArrayList<ArrayList<ScopeVariable>> scopeMacroAction, Map<String, ParsedAction> actionNameToObject,
            Map<String, ParsedMethod> methodNameToObject, boolean isFirstChildOfMethod) {
        this.macroAction = macroAction;
        this.parentFlow = parentFlow;
        this.scopeMacroAction = scopeMacroAction;
        this.isPrimitiveFlow = false;
        this.numberChildrenPrimitiveFlow = 0;

        // TODO, we should compute the precondition and effects of the macro action here
        // (or take them from a table since there will always be the same macro action)
        // For now, consider that there is only one action, and takes its preconditions
        // and effects
        ParsedAction liftedAction = actionNameToObject.get(macroAction.get(0));
        this.preconditions = liftedAction.getPreconditions();
        this.effects = liftedAction.getEffects();

        this.preconditions2 = new ArrayList<>();
        this.effects2 = new ArrayList<>();
        for (String actionName : macroAction) {
            ParsedAction liftedAction2 = actionNameToObject.get(actionName);
            this.preconditions2.add(liftedAction2.getPreconditions());
            this.effects2.add(liftedAction2.getEffects());
        }

        this.preconditionsHerited = new HashSet<CertifiedPredicate>();
        // If we are the first child of a method, we must inherit its preconditions
        if (isFirstChildOfMethod) {
            inheritPreconditionsFromParent(parentFlow, methodNameToObject);
        }

        this.rootsNodesWhichCanLedToThisFlow = new HashSet<LiftedFlow>();

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.inputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.outputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.preconditionPredicates = new HashSet<CertifiedPredicate>();

        this.uniqueId = LiftedFlow.numberLiftedFlow;
        LiftedFlow.numberLiftedFlow += macroAction.size(); // To have each subaction have a unique ID
    }

    // Use to create blank action
    public LiftedFlow(boolean isBlankAction, LiftedFlow parentFlow, Map<String, ParsedMethod> methodNameToObject,
            boolean isFirstChildOfMethod) {
        this.macroAction = new ArrayList<String>();
        this.macroAction.add("BLANK");
        this.parentFlow = parentFlow;
        this.scopeMacroAction = new ArrayList<>();
        this.scopeMacroAction.add(new ArrayList<>());
        this.isPrimitiveFlow = false;
        this.numberChildrenPrimitiveFlow = 0;

        this.preconditions2 = new ArrayList<>();
        this.effects2 = new ArrayList<>();

        this.preconditionsHerited = new HashSet<CertifiedPredicate>();
        // If we are the first child of a method, we must inherit its preconditions
        if (isFirstChildOfMethod) {
            inheritPreconditionsFromParent(parentFlow, methodNameToObject);
        }

        this.rootsNodesWhichCanLedToThisFlow = new HashSet<LiftedFlow>();

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.inputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.outputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.preconditionPredicates = new HashSet<CertifiedPredicate>();

        this.isBlankAction = true;
        this.uniqueId = LiftedFlow.numberLiftedFlow;
        LiftedFlow.numberLiftedFlow++;

    }

    public void setParentId(int parentId) {
        this.parentId = parentId;
    }

    public ArrayList<String> getMacroAction() {
        return this.macroAction;
    }

    public ArrayList<ScopeVariable> getScopeVariables() {
        return this.scopeMethod;
    }

    public ArrayList<ArrayList<ScopeVariable>> getScopeVariablesActionsFlow() {
        return this.scopeMacroAction;
    }

    public void setMethod(Method m) {
        this.method = m;
    }

    public void setMacroAction(ArrayList<String> macroAction) {
        this.macroAction = macroAction;
    }

    public void addNextLiftedFlow(LiftedFlow f) {
        this.nextsFlow.add(f);
    }

    public void addPreviousesLiftedFlow(LiftedFlow f) {
        this.previousesFlow.add(f);
    }

    public HashSet<LiftedFlow> getNextsLiftedFlow() {
        return this.nextsFlow;
    }

    public HashSet<LiftedFlow> getPreviousesLiftedFlow() {
        return this.previousesFlow;
    }

    public Integer getParentId() {
        return this.parentId;
    }

    public boolean isMethodLiftedFlow() {
        return this.methodName != null;
    }

    public Method getMethod() {
        return this.method;
    }

    public String getMethodName() {
        return this.methodName;
    }

    public void inheritPreconditionsFromParent(LiftedFlow parentFlow, Map<String, ParsedMethod> methodNameToObject) {

        // First, see if the parent method has already heritate precondition from its
        // parent node
        this.preconditionsHerited.addAll(parentFlow.preconditionsHerited);

        // By inherithing these predicates, we become de facto the certifier of these
        // predicates
        for (CertifiedPredicate pred : this.preconditionsHerited) {
            pred.certifiers.clear();
            pred.certifiers.add(this);
        }

        // Now add the precondition of the parent method in it
        ParsedMethod parentMethod = methodNameToObject.get(parentFlow.getMethodName());

        Expression<String> preconditionsMethod = parentMethod.getPreconditions();

        int numberPreMethod = preconditionsMethod.getChildren().size();
        if (numberPreMethod == 0 && preconditionsMethod.getSymbol() != null) {
            numberPreMethod = 1;
        }

        for (int preId = 0; preId < numberPreMethod; preId++) {

            Expression<String> pre;

            if (numberPreMethod > 1) {
                pre = preconditionsMethod.getChildren().get(preId);
            } else {
                pre = preconditionsMethod;
            }

            if (pre.getConnector().getImage().equals("true")) {
                continue;
            }

            boolean predicateIsPositive = true;

            // Negative predicate
            if (pre.getConnector().getImage().equals("not")) {
                predicateIsPositive = false;
                pre = pre.getChildren().get(0);
            }

            String namePredicate = pre.getSymbol().getValue();
            ArrayList<ScopeVariable> scopePred = new ArrayList<ScopeVariable>();

            for (Symbol<String> arg : pre.getArguments()) {
                int idxArg = Integer.parseInt(arg.getValue().substring(2));
                scopePred.add(parentFlow.scopeMethod.get(idxArg));
            }

            CertifiedPredicate certPredicate = new CertifiedPredicate(namePredicate, predicateIsPositive,
                    scopePred, this);

            this.preconditionsHerited.add(certPredicate);
        }
    }

    private ArrayList<ArrayList<CertifiedPredicate>> getCertifiedPredicateFromExpression(
            ArrayList<Expression<String>> preconditionOrEffectMacroAction, Map<String, ScopeVariable> dictConstantToScopeVariable) {

        ArrayList<ArrayList<CertifiedPredicate>> preOrEffMacroAction = new ArrayList<ArrayList<CertifiedPredicate>>();

        for (int actionIdx = 0; actionIdx < this.macroAction.size(); actionIdx++) {

            ArrayList<CertifiedPredicate> preOrEffAction = new ArrayList<CertifiedPredicate>();

            Expression<String> expresiionPreOfEffAction = preconditionOrEffectMacroAction.get(actionIdx);

            int numberPreActions = expresiionPreOfEffAction.getChildren().size();
            if (numberPreActions == 0 && expresiionPreOfEffAction.getSymbol() != null) {
                numberPreActions = 1;
            }

            for (int preId = 0; preId < numberPreActions; preId++) {

                Expression<String> pre;

                if (numberPreActions > 1) {
                    pre = expresiionPreOfEffAction.getChildren().get(preId);
                } else {
                    pre = expresiionPreOfEffAction;
                }

                if (pre.getConnector().getImage().equals("true")) {
                    continue;
                }

                boolean predicateIsPositive = true;

                // Negative predicate
                if (pre.getConnector().getImage().equals("not")) {
                    predicateIsPositive = false;
                    pre = pre.getChildren().get(0);
                }

                String namePredicate = pre.getSymbol().getValue();
                ArrayList<ScopeVariable> scopePred = new ArrayList<ScopeVariable>();

                for (Symbol<String> arg : pre.getArguments()) {
                    try {
                        int idxArg = Integer.parseInt(arg.getValue().substring(2));
                        scopePred.add(this.scopeMacroAction.get(actionIdx).get(idxArg));
                    } catch (Exception e) {
                        // It must be a constant, find the constant associated with it
                        if (!dictConstantToScopeVariable.containsKey(arg.getValue())) {
                            System.out.println("Error in the scope of the predicate " + namePredicate);
                            e.printStackTrace();
                            System.exit(0);
                        }
                        else {
                            scopePred.add(dictConstantToScopeVariable.get(arg.getValue()));
                        }
                    }
                }

                CertifiedPredicate certPredicate = new CertifiedPredicate(namePredicate, predicateIsPositive,
                        scopePred, this);

                preOrEffAction.add(certPredicate);
            }

            preOrEffMacroAction.add(preOrEffAction);
        }

        return preOrEffMacroAction;
    }

    public void computePreconditionsAndDefaultOutputCertifiedPredicates2(HashSet<String> staticPredicate,
            ArrayList<Candidate> liftedFamGroups, UnorderedPairDictionary<String, HashSet<Candidate>> dictPairPredicateNameToLiftedFamGroups, Map<String, ScopeVariable> dictConstantToScopeVariable) {

        ArrayList<ArrayList<CertifiedPredicate>> preconditionsAllActions;
        ArrayList<ArrayList<CertifiedPredicate>> effectsAllActions;

        if (!this.isBlankAction) {
            // First, get the preconditions by default of the macro action
            preconditionsAllActions = getCertifiedPredicateFromExpression(this.preconditions2, dictConstantToScopeVariable);

            // Get as well the effect of the macro action
            effectsAllActions = getCertifiedPredicateFromExpression(this.effects2, dictConstantToScopeVariable);
        } else {
            preconditionsAllActions = new ArrayList<ArrayList<CertifiedPredicate>>();
            preconditionsAllActions.add(new ArrayList<CertifiedPredicate>());

            effectsAllActions = new ArrayList<ArrayList<CertifiedPredicate>>();
            effectsAllActions.add(new ArrayList<CertifiedPredicate>());
        }

        // Add all the precondition of the parent method into the precondition of the
        // first action of the macro action if the action does not already satisfied it
        for (CertifiedPredicate preconditionsHerited : this.preconditionsHerited) {
            boolean canAddPreconditionHerited = true;
            for (CertifiedPredicate preconditionFirstAction : preconditionsAllActions.get(0)) {
                if (preconditionFirstAction.isEqualsTo(preconditionsHerited)) {
                    canAddPreconditionHerited = false;
                    break;
                }
            }
            if (canAddPreconditionHerited) {
                preconditionsAllActions.get(0).add(preconditionsHerited);
            }
        }

        // Ok, now is the difficult part
        // from the precondition and effects of all the actions of the method
        // we want to generate a unique new action with its own preconditions and
        // effects

        ArrayList<CertifiedPredicate> preconditionsMacroAction = new ArrayList<CertifiedPredicate>();
        HashSet<CertifiedPredicate> currentStateOfTheWorld = new HashSet<CertifiedPredicate>();

        HashSet<CertifiedPredicate> predicatesToRemove = new HashSet<CertifiedPredicate>();
        HashSet<CertifiedPredicate> predicatesToAdd = new HashSet<CertifiedPredicate>();
        Vector<Pair<ScopeVariable, ScopeVariable>> constrainsToBeInSameLiftedFamGroup = new Vector<Pair<ScopeVariable, ScopeVariable>>();


        for (int i = 0; i < this.macroAction.size(); i++) {

            // First, iterate over all the precondition of the current action
            if (i == 0) {
                // For the first action, we can directly add all the precondition into the precondition of the macro action
                // and into the state of the world
                for (CertifiedPredicate precondition : preconditionsAllActions.get(i)) {
                    preconditionsMacroAction.add(precondition);
                    currentStateOfTheWorld.add(precondition);
                }
            }
            else {
                // Iterate over all preconditions of the current action
                for (CertifiedPredicate precondition : preconditionsAllActions.get(i)) {
                    
                    // If the precondition is already into the state of the world, there is no need to add it into the precondition of the macro action
                    boolean preconditionAlreadyInStateOfTheWorld = false;
                    for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {
                        if (predCurrentStateOfTheWorld.isEqualsTo(precondition)) {
                            preconditionAlreadyInStateOfTheWorld = true;
                            break;
                        }
                    }

                    if (preconditionAlreadyInStateOfTheWorld) {
                        continue;
                    }

                    // Else we need to try to unify the precondition with each predicate of the state of the world
                    boolean cannotUnify = true;
                    for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {

                        // Two cases:
                        // 2) we have an unifier failure. It means that the precondition is not satisfied by the state of the world. We add it into the precondition of the macro action
                        // 3) we have an unifier success with constrains. We must add those constrains into the precondition of the macro action

                        // Iterate over all the possible unification
                        HashSet<Candidate> unificationsPossible = dictPairPredicateNameToLiftedFamGroups.get(precondition.predicateName, predCurrentStateOfTheWorld.predicateName);
                        if (unificationsPossible == null) {
                            continue;
                        }
                        
                        for (Candidate liftedFamGroup : unificationsPossible) {

                            constrainsToBeInSameLiftedFamGroup.clear();
                            // Try to unify thoses two predicates
                            LIFTED_FAM_GROUP_UNIFIER result = UnifyPredicates2(precondition, predCurrentStateOfTheWorld, liftedFamGroup, constrainsToBeInSameLiftedFamGroup);

                            if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
                                System.out.println("NOOOOP");
                                System.exit(0);
                            }
                            else if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {
                                cannotUnify = true;
                                for (Pair<ScopeVariable, ScopeVariable> scopeThatMustBeDifferent : constrainsToBeInSameLiftedFamGroup) {
                                    // We add the constrains for these two scope variables to be different
                                    scopeThatMustBeDifferent.getLeft().addConstrainsNotEqual(scopeThatMustBeDifferent.getRight());
                                    scopeThatMustBeDifferent.getRight().addConstrainsNotEqual(scopeThatMustBeDifferent.getLeft());
                                }
                                // break;
                            }
                            else {
                                // Do nothing
                            }

                            int a = 0;
                        }
                    }
                    if (cannotUnify) {
                        // We cannot unify the precondition with any predicate of the state of the world
                        // We add it into the precondition of the macro action
                        preconditionsMacroAction.add(precondition);
                        predicatesToAdd.add(precondition);
                    }
                    int b = 0;
                }
                currentStateOfTheWorld.addAll(predicatesToAdd);
                predicatesToAdd.clear();
            }

            predicatesToAdd.clear();
            predicatesToRemove.clear();

            // Then iterate over all the effects of the current action
            // First, iterate over all the negative effects
            for (CertifiedPredicate negEffect : effectsAllActions.get(i)) {
                if (negEffect.isPositive) {
                    continue;
                }

                // Try to unify the effect with each predicate of the state of the world
                for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {

                    // Iterate over all the possible unification
                    HashSet<Candidate> unificationsPossible = dictPairPredicateNameToLiftedFamGroups.get(negEffect.predicateName, predCurrentStateOfTheWorld.predicateName);
                    if (unificationsPossible == null) {
                        continue;
                    }
                    for (Candidate liftedFamGroup : unificationsPossible) {
                        constrainsToBeInSameLiftedFamGroup.clear();
                        // Try to unify thoses two predicates
                        LIFTED_FAM_GROUP_UNIFIER result = UnifyPredicates2(negEffect, predCurrentStateOfTheWorld, liftedFamGroup, constrainsToBeInSameLiftedFamGroup);
                        
                        if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
                            // Remove this predicate from the state of the world + add the predicate ALL_FALSE_<lifted_fam_group> into the state of the world
                            predicatesToRemove.add(predCurrentStateOfTheWorld);

                            AtomCandidate emptyLiftedFamGroup = liftedFamGroup.mutexGroup.get(0);
                            String NameliftedFamGroupEmpty = emptyLiftedFamGroup.predSymbolName;
                            ArrayList<ScopeVariable> argEmptyLiftedFamGroup = new ArrayList<ScopeVariable>();
                            for (AtomCandidate aC : liftedFamGroup.mutexGroup) {
                                if (aC.predSymbolName.equals(negEffect.predicateName)) {
                                    for (Integer idParam : emptyLiftedFamGroup.paramsId) {
                                        for (int k = 0; k < aC.paramsId.size(); k++) {
                                            if (aC.paramsId.get(k) == idParam) {
                                                argEmptyLiftedFamGroup.add(negEffect.scope.get(k));
                                                continue;
                                            }
                                        }
                                    }
                                    break;
                                }
                            }
                            // Add the certified predicate ALL_FALSE_<lifted_fam_group> into the state of the world
                            predicatesToAdd.add(new CertifiedPredicate(NameliftedFamGroupEmpty, true, argEmptyLiftedFamGroup, this));
                        }
                    }
                }
                currentStateOfTheWorld.addAll(predicatesToAdd);
                currentStateOfTheWorld.removeAll(predicatesToRemove);
            }

            predicatesToAdd.clear();
            predicatesToRemove.clear();





            // Now, we add the positive effect into the state of the world
            for (CertifiedPredicate posEffect : effectsAllActions.get(i)) {
                if (!posEffect.isPositive) {
                    continue;
                }

                // Try to unify the effect with each predicate of the state of the world
                for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {

                    // Iterate over all the possible unification
                    HashSet<Candidate> unificationsPossible = dictPairPredicateNameToLiftedFamGroups.get(posEffect.predicateName, predCurrentStateOfTheWorld.predicateName);
                    if (unificationsPossible == null) {
                        continue;
                    }

                    for (Candidate liftedFamGroup : unificationsPossible) {
                        constrainsToBeInSameLiftedFamGroup.clear();
                        // Try to unify thoses two predicates
                        LIFTED_FAM_GROUP_UNIFIER result = UnifyPredicates2(posEffect, predCurrentStateOfTheWorld, liftedFamGroup, constrainsToBeInSameLiftedFamGroup);
                        
                        if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
                            // Remove this predicate from the state of the world + add this predicate into the state of the world
                            predicatesToAdd.add(posEffect);
                            predicatesToRemove.add(predCurrentStateOfTheWorld);
                        }
                    }
                }
            }  
            
            currentStateOfTheWorld.addAll(predicatesToAdd);
            currentStateOfTheWorld.removeAll(predicatesToRemove);

            predicatesToAdd.clear();
            predicatesToRemove.clear();
        }

        // for (int i = 0; i < this.macroAction.size(); i++) {
        //     // For all precondition of this action that are not in the state of the world,
        //     // add them to the precondition of the macro action
        //     for (CertifiedPredicate precondition : preconditionsAllActions.get(i)) {
        //         boolean isInStateOfTheWorld = false;
        //         for (CertifiedPredicate predCurrentState : currentStateOfTheWorld) {
        //             if (precondition.isEqualsTo(predCurrentState)) {
        //                 isInStateOfTheWorld = true;
        //                 break;
        //             }
        //         }

        //         // If it not in the state of the world, we have to add it as precondition and
        //         // then consider that we have it into our world state
        //         if (!isInStateOfTheWorld) {

        //             // We are also forced to see if this predicate can be in the same SAS+ group with another
        //             // precondition. If that's the case, we must add constrains to prevent to have those two values equals
        //             // e.g for gripper, we have pick1->pick2->move3->drop4->drop5
        //             // and pick1 => free hand1, pick2 => free hand2
        //             // So on the precondition of the macro action, we must have hand1 != hand2
        //             for (CertifiedPredicate certifiedPre : preconditionsMacroAction) {

        //                 ArrayList<ScopeVariable> constrainsToBeInSameLiftedFamGroup = new ArrayList<ScopeVariable>();
        //                 for (int k = 0; k < precondition.scope.size(); k++) {
        //                     constrainsToBeInSameLiftedFamGroup.add(null);
        //                 }

        //                 LIFTED_FAM_GROUP_UNIFIER result = UnifyPredicates(precondition, certifiedPre, liftedFamGroups,
        //                         constrainsToBeInSameLiftedFamGroup);

        //                 if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
        //                     System.out.println("Path not implemented...");
        //                     System.exit(1);
        //                 } else if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {

        //                     int numConstrains = 0;
        //                     for (int argi = 0; argi < precondition.scope.size(); argi++) {
        //                         if (constrainsToBeInSameLiftedFamGroup.get(argi) != null) {
        //                             // System.out.println("Add constrains: " + pred1.scope.get(argi).getUniqueName()
        //                             // + " != " + pred2.scope.get(argi).getUniqueName());
        //                             precondition.scope.get(argi)
        //                                     .addConstrainsNotEqual(constrainsToBeInSameLiftedFamGroup.get(argi));

        //                             Map<ScopeVariable, HashSet<ScopeVariable>> constrains = new HashMap<ScopeVariable,HashSet<ScopeVariable>>();
        //                             constrains.put(precondition.scope.get(argi), new HashSet<ScopeVariable>());
        //                             constrains.get(precondition.scope.get(argi)).add(constrainsToBeInSameLiftedFamGroup.get(argi));
        //                             precondition.setConstrainsScope(constrains);
        //                         }
        //                         numConstrains++;
        //                     }

        //                     if (numConstrains > 1) {
        //                         System.out.println("Path not implemented...");
        //                         System.exit(1);
        //                     }
        //                 }
        //             }

        //             preconditionsMacroAction.add(precondition);
        //             currentStateOfTheWorld.add(precondition);
        //         }
        //     }

        //     // Now apply the effects of the action of the state of the world
        //     HashSet<Candidate> mutexToSetToFalse = new HashSet<Candidate>();
        //     for (CertifiedPredicate effect : effectsAllActions.get(i)) {
        //         // If there is an effect that is opposed to the state of the world, we remove
        //         // this predicate from the state of the world
        //         boolean usedToRemoveState = false;
        //         for (CertifiedPredicate predCurrentState : currentStateOfTheWorld) {
        //             if (effect.isOppositeTo(predCurrentState)) {
        //                 usedToRemoveState = true;
        //                 currentStateOfTheWorld.remove(predCurrentState);
        //                 break;
        //             }
        //         }

        //         if (!effect.isPositive) {
        //             // 
        //         }

        //         System.out.println("THERE ARE THINGS TO DO HERE. WE MUST AGAIN COMPUTE THE LIFTED FAM GROUPS");
        //         System.exit(1);
        //         if (!usedToRemoveState) 
        //         {
        //             currentStateOfTheWorld.add(effect);
        //         }
        //     }
        //     int a = 0;
        // }

        this.preconditionPredicates.addAll(preconditionsMacroAction);
        // Add all the state of the world into the effect of the macro action
        this.outputCertifiedPredicates.addAll(currentStateOfTheWorld);

        int a = 0;
    }

    public void computePreconditionsAndDefaultOutputCertifiedPredicates(HashSet<String> staticPredicates,
            ArrayList<Candidate> liftedFamGroups) {

        // If we are a blank action, we do not have precondition and effects
        if (this.isBlankAction) {
            return;
        }

        // So a precondition of the macro action is a precondition that is not already
        // been filled by the effect of a previous action of the macro action
        // In the same way, an effect of the macro action if an effect of an action if
        // the following actions do not remove this effect afterward

        ArrayList<CertifiedPredicate> currentPreconditionsMacroAction = new ArrayList<CertifiedPredicate>();
        ArrayList<CertifiedPredicate> currentEffectsMacroAction = new ArrayList<CertifiedPredicate>();

        HashSet<CertifiedPredicate> negativeEffs = new HashSet<>();

        for (int actionIdx = 0; actionIdx < this.macroAction.size(); actionIdx++) {

            HashSet<CertifiedPredicate> preconditionAction = new HashSet<CertifiedPredicate>();

            Expression<String> preconditionsAction = this.preconditions2.get(actionIdx);

            int numberPreActions = preconditionsAction.getChildren().size();
            if (numberPreActions == 0 && preconditionsAction.getSymbol() != null) {
                numberPreActions = 1;
            }

            for (int preId = 0; preId < numberPreActions; preId++) {

                Expression<String> pre;

                if (numberPreActions > 1) {
                    pre = preconditionsAction.getChildren().get(preId);
                } else {
                    pre = preconditionsAction;
                }

                if (pre.getConnector().getImage().equals("true")) {
                    continue;
                }

                boolean predicateIsPositive = true;

                // Negative predicate
                if (pre.getConnector().getImage().equals("not")) {
                    predicateIsPositive = false;
                    pre = pre.getChildren().get(0);
                }

                String namePredicate = pre.getSymbol().getValue();
                ArrayList<ScopeVariable> scopePred = new ArrayList<ScopeVariable>();

                for (Symbol<String> arg : pre.getArguments()) {
                    int idxArg = Integer.parseInt(arg.getValue().substring(2));
                    scopePred.add(this.scopeMacroAction.get(actionIdx).get(idxArg));
                }

                // TODO what to do for negative input certified predicate ?? Add them or
                // not add them (and consider all predicate which are not here as invariant
                // false ?)
                // Nope, we have to consider with the SAS+ to see if those candidates can have
                // multiple values

                CertifiedPredicate certPredicate = new CertifiedPredicate(namePredicate, predicateIsPositive,
                        scopePred, this);

                preconditionAction.add(certPredicate);

                // We can also add this precondition to the preconditon of the macro action if
                // we do not already have it
                boolean addPrecondition = true;
                for (CertifiedPredicate currentPrecondition : currentPreconditionsMacroAction) {
                    if (currentPrecondition.isEqualsTo(certPredicate)) {
                        addPrecondition = false;
                        break;
                    }
                }
                // We do not add this precondition if an effect already satisfied it
                for (CertifiedPredicate currentEffect : currentEffectsMacroAction) {
                    if (currentEffect.isEqualsTo(certPredicate)) {
                        addPrecondition = false;
                        break;
                    }
                }

                if (addPrecondition) {
                    currentPreconditionsMacroAction.add(certPredicate);
                }

            }

            Expression<String> effectsAction = this.effects2.get(actionIdx);

            // Compute the effects as well
            int numberEffActions = effectsAction.getChildren().size();
            if (numberEffActions == 0 && effectsAction.getSymbol() != null) {
                numberEffActions = 1;
            }

            for (int effId = 0; effId < numberEffActions; effId++) {

                Expression<String> eff;
                if (numberEffActions > 1) {
                    eff = effectsAction.getChildren().get(effId);
                } else {
                    eff = effectsAction;
                }

                if (eff.getConnector().getImage().equals("true")) {
                    continue;
                }

                boolean predicateIsPositive = true;

                // Negative predicate
                if (eff.getConnector().getImage().equals("not")) {
                    eff = eff.getChildren().get(0);
                    predicateIsPositive = false;
                }

                String namePredicate = eff.getSymbol().getValue();

                ArrayList<ScopeVariable> scopePred = new ArrayList<ScopeVariable>();

                for (Symbol<String> arg : eff.getArguments()) {
                    int idxArg = Integer.parseInt(arg.getValue().substring(2));
                    scopePred.add(this.scopeMacroAction.get(actionIdx).get(idxArg));
                }

                // Create the effect as a certified predicate
                CertifiedPredicate certifiedPred = new CertifiedPredicate(namePredicate, predicateIsPositive, scopePred,
                        this);

                if (!predicateIsPositive) {
                    // If we have an effect which is opposite to this negative effect, remove this
                    // effect and do not add the negative effect (since it has already been used to
                    // remove a positive predicate)
                    boolean negativeEffectCanRemovePositiveEffect = false;
                    for (CertifiedPredicate currentEffect : currentEffectsMacroAction) {
                        if (currentEffect.isOppositeTo(certifiedPred)) {
                            // negativeEffectCanRemovePositiveEffect = true;
                            currentEffectsMacroAction.remove(currentEffect);
                            break;
                        }
                    }

                    if (!negativeEffectCanRemovePositiveEffect) {
                        negativeEffs.add(certifiedPred);
                    }
                    continue;
                }

                // Now we can add the effect (Question do we add negative predicate or do we
                // cansider
                // all predicate which are not among the positive predicate as false ?)
                currentEffectsMacroAction.add(certifiedPred);
            }

            // Now, we add the preconditions into the currentEffects (only if there is not a
            // negative effects which remove this precondition)
            for (CertifiedPredicate precondition : preconditionAction) {

                boolean addThisPreconditionToEffects = true;
                for (CertifiedPredicate negEff : negativeEffs) {
                    if (negEff.isOppositeTo(precondition)) {
                        addThisPreconditionToEffects = false;
                        // Remove the negative effect as well since it has been "used" to remove this
                        // precondition
                        negativeEffs.remove(negEff);
                        break;
                    }
                }
                if (!addThisPreconditionToEffects) {
                    continue;
                }
                // To the same things with the positive effects
                for (CertifiedPredicate posEff : currentEffectsMacroAction) {
                    if (posEff.isEqualOrOppositeTo(precondition)) {
                        addThisPreconditionToEffects = false;
                        break;
                    }
                }
                if (!addThisPreconditionToEffects) {
                    continue;
                }

                // We can now add this precondition to the effect
                currentEffectsMacroAction.add(precondition);
            }

            for (int i = 0; i <= actionIdx; i++) {
                System.out.print(this.getMacroAction().get(i));
                if (i != actionIdx) {
                    System.out.print("->");
                }
            }

            System.out.println("\n=== preconditions ===");
            for (CertifiedPredicate precondition : currentPreconditionsMacroAction) {
                System.out.println(precondition);
            }
            System.out.println("=== effects ===");
            for (CertifiedPredicate effect : currentEffectsMacroAction) {
                System.out.println(effect);
            }
            System.out.println("=== neg effects ===");
            for (CertifiedPredicate effect : negativeEffs) {
                System.out.println(effect);
            }
            System.out.println("===========");
            int a = 0;
        }

        // Now, we have to see the constrains on the precondition and effect. Indeed,
        // we cannot have a state with multiple predicate in the same SAS+ group
        // which implies some constrains on the value of some scope
        for (int i = 0; i < currentPreconditionsMacroAction.size(); i++) {
            for (int j = i + 1; j < currentPreconditionsMacroAction.size(); j++) {

                CertifiedPredicate pred1 = currentPreconditionsMacroAction.get(i);
                CertifiedPredicate pred2 = currentPreconditionsMacroAction.get(j);

                ArrayList<ScopeVariable> constrainsToBeInSameLiftedFamGroup = new ArrayList<ScopeVariable>();
                for (int k = 0; k < pred1.scope.size(); k++) {
                    constrainsToBeInSameLiftedFamGroup.add(null);
                }

                // Now, try to unify the two predicate
                LIFTED_FAM_GROUP_UNIFIER resultUnification = UnifyPredicates(pred1, pred2, liftedFamGroups,
                        constrainsToBeInSameLiftedFamGroup);

                // Multiple case here

                // If there is no way that those two predicates can be unified, we have nothing
                // to do here
                if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.FAILED) {
                    continue;
                }

                else if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
                    System.out.println("Should not happened !");
                    System.exit(1);
                }

                // If they can unify only with specific constrains
                else if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {

                    // We must do everything to prevent those two from being equal
                    // For now, we just imagine there is only one constrains (we will see layer for
                    // multiple constrains)

                    int numConstrains = 0;

                    for (int argi = 0; argi < pred1.scope.size(); argi++) {
                        if (constrainsToBeInSameLiftedFamGroup.get(argi) != null) {
                            System.out.println("Add constrains: " + pred1.scope.get(argi).getUniqueName() + " != "
                                    + pred2.scope.get(argi).getUniqueName());
                            pred1.scope.get(argi).addConstrainsNotEqual(constrainsToBeInSameLiftedFamGroup.get(argi));
                        }

                        numConstrains++;
                    }

                    if (numConstrains > 1) {
                        System.out.println("I do not know how to handle this !");
                        System.exit(1);
                    }
                }
            }
        }

        // TODO do we have to add negative predicates of the macro action ?
        // I think we don't have to add them if we already have another in the same SAS+
        // group that this predicate
        // (which should always happend I guess)

        // Now add all precondition only if this is not a static precondition and the
        // effect has not removed this precondition
        // for (CertifiedPredicate precondition : currentPreconditionsMacroAction) {
        // if (staticPredicates.contains(precondition.predicateName)) {
        // continue;
        // }
        // boolean oppositePredIsInEffect = false;
        // for (CertifiedPredicate certifiedEff : currentEffectsMacroAction) {
        // if (certifiedEff.isEqualOrOppositeTo(precondition)) {
        // oppositePredIsInEffect = true;
        // break;
        // }
        // }
        // for (CertifiedPredicate negEff : negativeEffs) {
        // if (negEff.isOppositeTo(precondition)) {
        // oppositePredIsInEffect = true;
        // break;
        // }
        // }
        // if (!oppositePredIsInEffect) {
        // currentEffectsMacroAction.add(precondition);
        // }
        // }

        this.preconditionPredicates.addAll(currentPreconditionsMacroAction);
        this.outputCertifiedPredicates.addAll(currentEffectsMacroAction);
    }

    public void updateOutputCertifiedPredicateWithCertifiedInputPredicate(HashSet<String> staticPredicates,
            ArrayList<Candidate> liftedFamGroups, UnorderedPairDictionary<String, HashSet<Candidate>> dictPairPredicateNameToLiftedFamGroups) {

        HashSet<CertifiedPredicate> inputCertifiedPredThatMustBeTransmit = new HashSet<>();

        Vector<Pair<ScopeVariable, ScopeVariable>> constrainsToBeInSameLiftedFamGroup = new Vector<Pair<ScopeVariable, ScopeVariable>>();

        // Now for each certified input, we only add it if we do not already certified
        // it
        for (CertifiedPredicate inputCertifiedPred : this.inputCertifiedPredicates) {

            boolean canBePruned = false;

            if (inputCertifiedPred.predicateName.equals("=")) {
                // We do not want to unify equal predicate, and there is no need to transmit
                // this predicate
                // to the output (I think. Instead, we will add the constrains to the relevant scope)
                canBePruned = true;
            }

            else {

                // Check if this certified predicate can be unified with one of our output
                // certificate
            //     for (CertifiedPredicate outpuCertifiedPredicate : this.outputCertifiedPredicates) {

            //         // Initialize an array of constrains which will indicate which contrains should
            //         // be filled
            //         // for the two predicate to be in the same lifted fam group
            //         ArrayList<ScopeVariable> constrainsToBeInSameLiftedFamGroup = new ArrayList<ScopeVariable>();
            //         for (int i = 0; i < inputCertifiedPred.scope.size(); i++) {
            //             constrainsToBeInSameLiftedFamGroup.add(null);
            //         }

            //         LIFTED_FAM_GROUP_UNIFIER resultUnification = UnifyPredicates(inputCertifiedPred,
            //                 outpuCertifiedPredicate, liftedFamGroups, constrainsToBeInSameLiftedFamGroup);

            //         if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
            //             // We can prune this predicate
            //             canBePruned = true;
            //             break;
            //         } else if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {
            //             // We have to add those constrains
            //             for (int i = 0; i < constrainsToBeInSameLiftedFamGroup.size(); i++) {
            //                 if (constrainsToBeInSameLiftedFamGroup.get(i) != null) {
            //                     inputCertifiedPred.addOutputConstrains(inputCertifiedPred.scope.get(i),
            //                             constrainsToBeInSameLiftedFamGroup.get(i));
            //                 }
            //             }
            //             int ici = 0;
            //         }
            //     }
            // }

                for (CertifiedPredicate outputCertifiedPredicate : this.outputCertifiedPredicates) {
                

                    // Iterate over all the possible unification
                    HashSet<Candidate> unificationsPossible = dictPairPredicateNameToLiftedFamGroups.get(inputCertifiedPred.predicateName, outputCertifiedPredicate.predicateName);
                    if (unificationsPossible == null) {
                        continue;
                    }
                    
                    for (Candidate liftedFamGroup : unificationsPossible) {

                        constrainsToBeInSameLiftedFamGroup.clear();
                        // Try to unify thoses two predicates
                        LIFTED_FAM_GROUP_UNIFIER result = UnifyPredicates2(inputCertifiedPred, outputCertifiedPredicate, liftedFamGroup, constrainsToBeInSameLiftedFamGroup);

                        if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
                            // No need to transmit this predicate
                            canBePruned = true;
                            break;
                        } else if (result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {
                            // We have to add those constrains
                            for (int i = 0; i < constrainsToBeInSameLiftedFamGroup.size(); i++) {
                                // if (constrainsToBeInSameLiftedFamGroup.get(i) != null) {
                                //     inputCertifiedPred.addOutputConstrains(inputCertifiedPred.scope.get(i),
                                //             constrainsToBeInSameLiftedFamGroup.get(i));
                                // }
                                inputCertifiedPred.addOutputConstrains(constrainsToBeInSameLiftedFamGroup.get(i).getLeft(), constrainsToBeInSameLiftedFamGroup.get(i).getRight());
                                
                            }
                        }
                        else {
                            // Do nothing
                        }

                        int a = 0;
                    }

                    if (canBePruned) {
                        break;
                    }
                }

                if (!canBePruned) {
                    inputCertifiedPredThatMustBeTransmit.add(inputCertifiedPred);
                }
            }
        }

        this.outputCertifiedPredicates.addAll(inputCertifiedPredThatMustBeTransmit);
    }

    // Will be useful to know if we must check the initial predicate to satisfy a
    // precondition
    public void getAllRootsNodeThatCanLedToThisFlowFromParents(HashSet<LiftedFlow> allParentsNode) {
        for (LiftedFlow parentNode : allParentsNode) {
            this.rootsNodesWhichCanLedToThisFlow.addAll(parentNode.rootsNodesWhichCanLedToThisFlow);
        }
    }

    public void computeInputCertifiedPredicatesFromParents(HashSet<LiftedFlow> allParentsNode) {

        int numParents = allParentsNode.size();

        boolean isLastParentNode = false;
        int idxParent = 0;

        HashSet<CertifiedPredicate> allHeritateCertPredToAdd = new HashSet<CertifiedPredicate>();

        for (LiftedFlow parentNode : allParentsNode) {

            HashSet<CertifiedPredicate> certPredsToAdd = new HashSet<CertifiedPredicate>();

            idxParent++;
            if (idxParent == allParentsNode.size()) {
                isLastParentNode = true;
            }

            // Add the certified predicate only if we do not contain it ourself
            // and if we do not contains the opposite of this predicate ourself
            for (CertifiedPredicate certPredParent : parentNode.outputCertifiedPredicates) {

                // Check if we do contains this certified predicate
                boolean alreadyContainsCertifiedPred = false;
                for (CertifiedPredicate ownCertifiedPredicate : this.inputCertifiedPredicates) {
                    if (ownCertifiedPredicate.isEqualsTo(certPredParent)) {
                        alreadyContainsCertifiedPred = true;
                        break;
                    }
                }

                // TODO what to do if the certified predicate is opposite to
                // out own input certified predicate (i.e, this path is impossible ?)

                if (alreadyContainsCertifiedPred) {
                    continue;
                }

                // Now we can add the certified predicate into our heritate certified predicate
                // If we already have a identical certified predicate that we have heritate from
                // another
                // parent, update it to tell that we can add this certified predicate from this
                // parent as well
                boolean predicateIsAlreadyHeritate = false;
                for (CertifiedPredicate heritateCertifiedPred : allHeritateCertPredToAdd) {
                    if (heritateCertifiedPred.isEqualsTo(certPredParent)) {
                        heritateCertifiedPred.certifiers.add(parentNode);

                        // Little optimization here, if all of our parent can certified a predicate, we
                        // remove it
                        // from the heritate certified predicates and put it into our own certified
                        // predicates
                        // (because any path from the inital action to this node will mandatory
                        // certified this predicate)
                        if (isLastParentNode && heritateCertifiedPred.certifiers.size() == allParentsNode.size()
                                && heritateCertifiedPred.certifiers.equals(allParentsNode)) {
                            heritateCertifiedPred.certifiers.clear();
                            heritateCertifiedPred.certifiers.add(this);
                        }

                        predicateIsAlreadyHeritate = true;
                        break;
                    }
                }

                if (!predicateIsAlreadyHeritate) {
                    // Create our new certified predicate
                    CertifiedPredicate heritateCertifiedPred;
                    // If we only have one parent and it is him who
                    // certify a predicate, we can certified it ourself:
                    // add this certified predicate as our own certified predicate (TODO not so
                    // simple here...)
                    if (numParents == 1 && certPredParent.certifiers.contains(parentNode)) {
                        heritateCertifiedPred = new CertifiedPredicate(certPredParent.predicateName,
                                certPredParent.isPositive, certPredParent.scope, this);

                        heritateCertifiedPred.setConstrainsScope(certPredParent.outputConstrainsScope);
                        certPredsToAdd.add(heritateCertifiedPred);
                    } else {
                        heritateCertifiedPred = new CertifiedPredicate(certPredParent.predicateName,
                                certPredParent.isPositive, certPredParent.scope, certPredParent.certifiers);
                        heritateCertifiedPred.setConstrainsScope(certPredParent.outputConstrainsScope);
                        certPredsToAdd.add(heritateCertifiedPred);
                    }
                }
            }
            allHeritateCertPredToAdd.addAll(certPredsToAdd);
        }
        this.inputCertifiedPredicates.addAll(allHeritateCertPredToAdd);
    }

    public void determinateHowToResolvePreconditions(HashSet<String> staticPredicates,
            ArrayList<Candidate> liftedFamGroups) {

        this.preconditionSolver = new HashMap<>();

        for (CertifiedPredicate precondition : this.preconditionPredicates) {

            if (staticPredicates.contains(precondition.predicateName)) {
                SolverPrecondition solverPrecondition = new SolverPrecondition();
                solverPrecondition.isStaticPrecondition = true;
                this.preconditionSolver.put(precondition, solverPrecondition);
                continue;
            }

            // Create the object which indicate how this precondition will be solved
            SolverPrecondition solverPrecondition = new SolverPrecondition();

            boolean shouldCheckInitialPred = true;

            // Iterate over all our certified input predicate
            for (CertifiedPredicate inputCertifiedPredicate : this.inputCertifiedPredicates) {

                HashSet<LiftedFlow> pathRootNodeToNodesWhichCanUnifyWithThisPred = new HashSet<LiftedFlow>();

                // Check if the precondition and the inputCertifiedPredicate can be in the same
                // liftedFamGroup

                // Initialize an array of constrains which will indicate which contrains should
                // be filled
                // for the two predicate to be in the same lifted fam group
                ArrayList<ScopeVariable> constrainsToBeInSameLiftedFamGroup = new ArrayList<ScopeVariable>();
                for (int i = 0; i < precondition.scope.size(); i++) {
                    constrainsToBeInSameLiftedFamGroup.add(null);
                }

                // Now, try to unify the two predicate
                LIFTED_FAM_GROUP_UNIFIER resultUnification = UnifyPredicates(precondition, inputCertifiedPredicate,
                        liftedFamGroups, constrainsToBeInSameLiftedFamGroup);

                // Multiple case here

                // If there is no way that those two predicates can be unified, we have nothing
                // to do here
                if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.FAILED) {
                    continue;
                }

                // If this is a success, it means that this precondition cannot be executed if
                // this predicate is true
                // Except if all the value in the preconditions parameters are the same as the
                // value in the inputCertifiedPredicate
                // (i.e: that's the same predicate)
                else if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {

                    boolean allScopeVarAreIdentical = true;
                    for (int argi = 0; argi < precondition.scope.size(); argi++) {
                        String val1 = precondition.scope.get(argi).getUniqueName();
                        String val2 = inputCertifiedPredicate.scope.get(argi).getUniqueName();
                        if (!val1.equals(val2)) {
                            allScopeVarAreIdentical = false;
                            // Those two must be equals
                            solverPrecondition.scopeVarThatMustBeEquals.add(
                                    Triple.of(inputCertifiedPredicate.certifiers, precondition.scope.get(argi),
                                            inputCertifiedPredicate.scope.get(argi)));
                        }
                    }

                    if (allScopeVarAreIdentical) {
                        // It means that we are confirming this precondition with our input certificate,
                        // this precondition should ne be checked
                        // It can only be true is all argument are identical

                        if (inputCertifiedPredicate.certifiers.contains(this)) {
                            solverPrecondition.isInvariantTrue = true;
                            shouldCheckInitialPred = false;
                        } else {
                            // We must indicate that the precondition is true is the path go to the
                            // certifier predicate
                            solverPrecondition.trueIfPassingByThoseFLows.addAll(inputCertifiedPredicate.certifiers);
                        }
                    }

                    if (inputCertifiedPredicate.certifiers.contains(this)) {
                        shouldCheckInitialPred = false;
                    } else {
                        for (LiftedFlow certifiers : inputCertifiedPredicate.certifiers) {
                            pathRootNodeToNodesWhichCanUnifyWithThisPred
                                    .addAll(certifiers.rootsNodesWhichCanLedToThisFlow);
                        }

                        if (pathRootNodeToNodesWhichCanUnifyWithThisPred.equals(this.rootsNodesWhichCanLedToThisFlow)) {
                            shouldCheckInitialPred = false;
                        }
                    }

                }

                // If they can unify only with speicific constrains
                else if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {
                    // Add the constrains here, the pred to add can only be true
                    // if it doesn't violate the constrains

                    int numConstrains = 0;

                    for (int argi = 0; argi < precondition.scope.size(); argi++) {
                        if (constrainsToBeInSameLiftedFamGroup.get(argi) != null) {

                            ScopeVariable pivotConstrain = inputCertifiedPredicate.scope.get(argi);
                            if (precondition.scope.get(argi).getPossibleValueVariable().size() == 1
                                    && !precondition.scope.get(argi).getUniqueName()
                                            .equals(inputCertifiedPredicate.scope.get(argi)
                                                    .getUniqueName())) {
                                // This constrains will never be functionnal
                                continue;
                            }

                            // Check if we have a contrains that prevent this predicate to be true
                            if (inputCertifiedPredicate.inputConstrainsScope
                                    .containsKey(pivotConstrain)
                                    && inputCertifiedPredicate.inputConstrainsScope
                                            .get(pivotConstrain).contains(precondition.scope.get(argi))) {
                                continue;
                            }

                            if (inputCertifiedPredicate.scope.size() == 1) {
                                precondition.scope.get(argi).addConstrainsOnScopeVariable(
                                        pivotConstrain,
                                        this,
                                        null,
                                        null,
                                        inputCertifiedPredicate.inputConstrainsScope.get(pivotConstrain));
                            }

                            for (int i = 0; i < inputCertifiedPredicate.scope.size(); i++) {
                                if (i != argi) {
                                    // TODO, we have to add the constrains of the inputCertifiedPredicate here !!!
                                    // precondition.scope.get(argi).addConstrains(pivotConstrain,
                                    // precondition.scope.get(i),
                                    // inputCertifiedPredicate.scope.get(i), this);

                                    precondition.scope.get(argi).addConstrainsOnScopeVariable(
                                            pivotConstrain,
                                            this,
                                            precondition.scope.get(i),
                                            inputCertifiedPredicate.scope.get(i),
                                            inputCertifiedPredicate.inputConstrainsScope.get(pivotConstrain));
                                }
                            }
                            solverPrecondition.constrainsOnScope.add(precondition.scope.get(argi));
                            numConstrains++;
                        }
                    }

                    if (numConstrains > 1) {
                        System.out.println("I do not know how to handle this !");
                        System.exit(1);
                    }

                    // Check who is the certifier
                    if (inputCertifiedPredicate.certifiers.contains(this)) {
                        // It means that we can only solve this precondition is the constrains is filled
                        // Else, we should check the initial value

                    } else {
                        int b = 0;
                        System.out.println("PATH NOT IMPLEMENTED ! ");
                        System.exit(1);
                    }
                }
            }

            if (shouldCheckInitialPred) {
                solverPrecondition.mustCheckInitValue = true;
            }

            this.preconditionSolver.put(precondition, solverPrecondition);
        }
    }

    /**
     * A predicate is SAS+ pruned, if whatever the value that takes the scope of the
     * predicate to check,
     * there is already a predicate in the effects that is among the same lifted fam
     * group
     * 
     * @param predicateToCheck
     * @param liftedFamGroup
     * @return
     */
    public boolean predicateCanBeSASPlusPruned(CertifiedPredicate predicateToCheck, Candidate liftedFamGroup,
            AtomCandidate atomThatCanBeBound) {

        HashSet<AtomVariable> varsBoundByPredicateToCheck = new HashSet<AtomVariable>();

        // First bound the predicate to check
        for (int argi = 0; argi < predicateToCheck.scope.size(); argi++) {
            AtomVariable var = liftedFamGroup.variables.get(atomThatCanBeBound.paramsId.get(argi));

            // If the variable is a counted variable, it can take any value, there is no
            // need to bound
            if (var.isCountedVar) {
                continue;
            }
            // If the predicate to check can take multiple value for this argument, and the
            // lifted fam
            // group can only takes one argument, then we cannot check for lifte fam group
            // here...
            // e.g: predicate to check: in {pkg_0, pkg_1} {truck_0, truck_1} and lifted fam
            // group is (in V0: pkg C0: truck}
            // we can have as effect both in pkg_0 truck_0 and in pkg_1 truck_1)
            else if (predicateToCheck.scope.get(argi).getPossibleValueVariable().size() > 1) {

                // Here we can bound the variable with the name of the scope value.
                var.value = predicateToCheck.scope.get(argi).getUniqueName();
                varsBoundByPredicateToCheck.add(var);
            } else {
                // Bound the variable
                var.value = predicateToCheck.scope.get(argi).getPossibleValueVariable().iterator().next();
                varsBoundByPredicateToCheck.add(var);
            }
        }

        // Now, iterate over all effects of the lifted flow and see if another lifted
        // flow can be bound to this liftedFamGroup
        for (CertifiedPredicate outputCertifiedPredicate : this.outputCertifiedPredicates) {

            for (AtomCandidate atomCandidate : liftedFamGroup.mutexGroup) {
                if (atomCandidate.predSymbolName.equals(outputCertifiedPredicate.predicateName)) {

                    boolean canBeRepresentedByLiftedFamGroup = true;
                    // Check if the type of each arg is also identical
                    for (int argi = 0; argi < outputCertifiedPredicate.scope.size(); argi++) {
                        AtomVariable var = liftedFamGroup.variables.get(atomCandidate.paramsId.get(argi));
                        if (!var.typeName.equals(outputCertifiedPredicate.scope.get(argi).getType())) {
                            canBeRepresentedByLiftedFamGroup = false;
                            break;
                        }
                        // Bound the variable
                        if (var.isCountedVar) {
                            continue;
                        } else if (outputCertifiedPredicate.scope.get(argi).getPossibleValueVariable().size() > 1) {
                            String valueOutputCertifiedPredArgi = outputCertifiedPredicate.scope.get(argi)
                                    .getUniqueName();
                            // Check if the variable is correctly bound by the predicate to check
                            if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                                // It's correct here, we can continue
                                continue;
                            } else {
                                // The var is bound to another value... No correct here
                                canBeRepresentedByLiftedFamGroup = false;
                                break;
                            }
                        } else {
                            String valueOutputCertifiedPredArgi = outputCertifiedPredicate.scope.get(argi)
                                    .getPossibleValueVariable().iterator().next();
                            // Check if the variable is correctly bound by the predicate to check
                            if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                                // It's correct here, we can continue
                                continue;
                            } else {
                                // The var is bound to another value... No correct here
                                canBeRepresentedByLiftedFamGroup = false;
                                break;
                            }
                        }

                    }
                    if (!canBeRepresentedByLiftedFamGroup) {
                        continue;
                    }
                    // Else, it means that we already have a predicate of the lifted fam ground in
                    // output
                    // Clean the variable
                    for (AtomVariable varBound : varsBoundByPredicateToCheck) {
                        varBound.value = null;
                    }
                    return true;
                }
            }
        }

        // Clean the variables
        for (AtomVariable varBound : varsBoundByPredicateToCheck) {
            varBound.value = null;
        }
        return false;
    }

    // With also indicate the constrains that must be met for the two predicates to
    // be in the same lifted fam group
    //
    private ReturnValueLiftedFamGroup predicateIsInSameLiftedFamGroupAsOutputPred(CertifiedPredicate predicateToCheck,
            Candidate liftedFamGroup, AtomCandidate atomThatCanBeBound,
            ArrayList<ScopeVariable> constrainsToSuccessfullyUnify, boolean compareWithInputCertifiedPredicate) {

        HashSet<AtomVariable> varsBoundByPredicateToCheck = new HashSet<AtomVariable>();

        // First bound the predicate to check
        for (int argi = 0; argi < predicateToCheck.scope.size(); argi++) {
            AtomVariable var = liftedFamGroup.variables.get(atomThatCanBeBound.paramsId.get(argi));

            // If the variable is a counted variable, it can take any value, there is no
            // need to bound
            if (var.isCountedVar) {
                continue;
            }
            // If the predicate to check can take multiple value for this argument, and the
            // lifted fam
            // group can only takes one argument, then we cannot check for lifte fam group
            // here...
            // e.g: predicate to check: in {pkg_0, pkg_1} {truck_0, truck_1} and lifted fam
            // group is (in V0: pkg C0: truck}
            // we can have as effect both in pkg_0 truck_0 and in pkg_1 truck_1)
            else if (predicateToCheck.scope.get(argi).getPossibleValueVariable().size() > 1) {

                // Here we can bound the variable with the name of the scope value.
                var.value = predicateToCheck.scope.get(argi).getUniqueName();
                varsBoundByPredicateToCheck.add(var);
            } else {
                // Bound the variable
                var.value = predicateToCheck.scope.get(argi).getPossibleValueVariable().iterator().next();
                varsBoundByPredicateToCheck.add(var);
            }
        }

        HashSet<CertifiedPredicate> predicatesToIterate;
        if (compareWithInputCertifiedPredicate) {
            predicatesToIterate = this.inputCertifiedPredicates;
        } else {
            predicatesToIterate = this.outputCertifiedPredicates;
        }

        // Priviligie the predicate without constrains on them (VERY UGLYYYYYYYY)
        ArrayList<CertifiedPredicate> orderedPredicateToIerate = new ArrayList<CertifiedPredicate>();
        for (CertifiedPredicate predicate : predicatesToIterate) {
            if (predicate.inputConstrainsScope.size() > 0) {
                orderedPredicateToIerate.add(predicate);
            } else {
                orderedPredicateToIerate.add(0, predicate);
            }
        }

        // Now, iterate over all effects of the lifted flow and see if another lifted
        // flow can be bound to this liftedFamGroup
        for (CertifiedPredicate outputCertifiedPredicate : orderedPredicateToIerate) {

            for (AtomCandidate atomCandidate : atomThatCanBeBound.candidateParent.mutexGroup) {
                if (atomCandidate.predSymbolName.equals(outputCertifiedPredicate.predicateName)) {

                    // First, check if there is a constrains on this predciate which prevent the
                    // unification
                    boolean cannotUnifyBecauseConstrains = false;
                    for (int argi = 0; argi < outputCertifiedPredicate.scope.size(); argi++) {
                        ScopeVariable var = outputCertifiedPredicate.scope.get(argi);
                        // Check if there is a constrains on this scopeVariable
                        if (outputCertifiedPredicate.inputConstrainsScope.containsKey(var)
                                && outputCertifiedPredicate.inputConstrainsScope.get(var)
                                        .contains(predicateToCheck.scope.get(argi))) {
                            cannotUnifyBecauseConstrains = true;
                            break;
                        }
                        // Check if they cannot be unified because we are sure that they cannot take the
                        // same variable
                        if (predicateToCheck.scope.get(argi).getPossibleValueVariable().size() == 1
                                && outputCertifiedPredicate.scope.get(argi).getPossibleValueVariable().size() == 1
                                && !predicateToCheck.scope.get(argi).getUniqueName()
                                        .equals(outputCertifiedPredicate.scope.get(argi).getUniqueName())) {
                            cannotUnifyBecauseConstrains = true;
                            break;
                        }
                    }
                    if (cannotUnifyBecauseConstrains) {
                        break;
                    }

                    boolean canBeRepresentedByLiftedFamGroup = true;
                    boolean needsConstrainsToBeRepresentedByLiftedFamGroup = false;
                    // Check if the type of each arg is also identical
                    for (int argi = 0; argi < outputCertifiedPredicate.scope.size(); argi++) {
                        AtomVariable var = atomCandidate.candidateParent.variables
                                .get(atomCandidate.paramsId.get(argi));
                        if (!var.typeName.equals(outputCertifiedPredicate.scope.get(argi).getType())) {

                            canBeRepresentedByLiftedFamGroup = false;
                            break;
                        }
                        // Bound the variable
                        if (var.isCountedVar) {
                            continue;
                        } else if (outputCertifiedPredicate.scope.get(argi).getPossibleValueVariable().size() > 1) {
                            String valueOutputCertifiedPredArgi = outputCertifiedPredicate.scope.get(argi)
                                    .getUniqueName();
                            // Check if the variable is correctly bound by the predicate to check
                            if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                                // It's correct here, we can continue
                                continue;
                            } else {
                                // The var is bound to another value... We need to indicate the constrains here
                                constrainsToSuccessfullyUnify.set(argi, outputCertifiedPredicate.scope.get(argi));
                                needsConstrainsToBeRepresentedByLiftedFamGroup = true;
                                // break;
                            }
                        } else {
                            String valueOutputCertifiedPredArgi = outputCertifiedPredicate.scope.get(argi)
                                    .getPossibleValueVariable()
                                    .iterator().next();
                            // Check if the variable is correctly bound by the predicate to check
                            if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                                // It's correct here, we can continue
                                continue;
                            } else {

                                // The var is bound to another value... No correct here
                                constrainsToSuccessfullyUnify.set(argi, outputCertifiedPredicate.scope.get(argi));
                                needsConstrainsToBeRepresentedByLiftedFamGroup = true;
                                // break;
                            }
                        }

                    }

                    if (!canBeRepresentedByLiftedFamGroup) {
                        continue;
                    }

                    // If we are here, it means that this predicate and a predicate in the output
                    // certified predicate
                    // are in the same lifted fam group (potentialy with constrains)

                    // Clean the variables
                    for (AtomVariable varBound : varsBoundByPredicateToCheck) {
                        varBound.value = null;
                    }

                    if (needsConstrainsToBeRepresentedByLiftedFamGroup) {
                        return new ReturnValueLiftedFamGroup(LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS,
                                outputCertifiedPredicate);
                    } else {
                        return new ReturnValueLiftedFamGroup(LIFTED_FAM_GROUP_UNIFIER.SUCCESS,
                                outputCertifiedPredicate);
                    }
                }
            }
        }

        // Clean the variables
        for (AtomVariable varBound : varsBoundByPredicateToCheck) {
            varBound.value = null;
        }

        return new ReturnValueLiftedFamGroup(LIFTED_FAM_GROUP_UNIFIER.FAILED, null);
    }

    /**
     * Try to unify two predicates in a lifted fam group
     * 
     * @param pred1
     * @param pred2
     * @param liftedFamGroups
     * @param constrainsToSuccessfullyUnify
     * @return
     */
    private LIFTED_FAM_GROUP_UNIFIER UnifyPredicates(CertifiedPredicate pred1, CertifiedPredicate pred2,
            ArrayList<Candidate> liftedFamGroups, ArrayList<ScopeVariable> constrainsToSuccessfullyUnify) {

        // First, try to find a lifted fam group which contains the predicate 1 and the
        // predicate 2.
        // If it doesn't exist, return ReturnValueLiftedFamGroup.FAILED
        LiftedFamGroupUnificateur liftedMutexGroupUnificateur = getLiftedFamGroupWhichContainsPredicates(pred1, pred2,
                liftedFamGroups);
        if (liftedMutexGroupUnificateur == null) {
            return LIFTED_FAM_GROUP_UNIFIER.FAILED;
        }

        Candidate liftedFamGroup = liftedMutexGroupUnificateur.liftedFamGroup;
        AtomCandidate atomThatCanBeBoundWithPred1 = liftedMutexGroupUnificateur.atomWhichCanUnifyWithPred1;
        AtomCandidate atomThatCanBeBoundWithPred2 = liftedMutexGroupUnificateur.atomWhichCanUnifyWithPred2;

        HashSet<AtomVariable> varsBoundByPredicateToClean = new HashSet<AtomVariable>();
        boolean needsConstrainsToBeInSameLiftedFamGroup = false;

        // First, check if there is a constrains on this predciate which prevent the
        // unification (TODO: not very proper here, beacuse we consider that the two
        // predicate have
        // the same signature which is not always the case)
        boolean cannotUnifyBecauseConstrains = false;
        for (int argi = 0; argi < pred1.scope.size(); argi++) {
            ScopeVariable var = pred1.scope.get(argi);
            // Check if there is a constrains on this scopeVariable
            if (pred1.inputConstrainsScope.containsKey(var)
                    && pred1.inputConstrainsScope.get(var)
                            .contains(pred2.scope.get(argi))) {
                cannotUnifyBecauseConstrains = true;
                break;
            }
        }

        if (cannotUnifyBecauseConstrains) {
            return LIFTED_FAM_GROUP_UNIFIER.FAILED;
        }

        // Now try to unify those two candidates

        // First bound the 1st predicate
        for (int argi = 0; argi < pred1.scope.size(); argi++) {
            AtomVariable var = liftedFamGroup.variables.get(atomThatCanBeBoundWithPred1.paramsId.get(argi));

            // If the variable is a counted variable, it can take any value, there is no
            // need to bound
            if (var.isCountedVar) {
                continue;
            } else if (pred1.scope.get(argi).getPossibleValueVariable().size() > 1) {

                // Here we can bound the variable with the name of the scope value.
                var.value = pred1.scope.get(argi).getUniqueName();
                varsBoundByPredicateToClean.add(var);
            } else {
                var.value = pred1.scope.get(argi).getPossibleValueVariable().iterator().next();
                varsBoundByPredicateToClean.add(var);
            }
        }

        // Now try to unify the second predicate with those constrains
        for (int argi = 0; argi < pred2.scope.size(); argi++) {
            AtomVariable var = liftedFamGroup.variables.get(atomThatCanBeBoundWithPred2.paramsId.get(argi));

            if (var.isCountedVar) {
                continue;
            }

            else {
                String nameArgiPred2 = pred2.scope.get(argi).getUniqueName();
                // Check if the variable is correctly bound by the predicate to check
                if (var.value != null && var.value.equals(nameArgiPred2)) {
                    // It's correct here, we can continue
                    continue;
                } else {
                    // The var is bound to another value...
                    // if the var is bound to a unique value that the predicate 2 cannot take,
                    // we are sure that we cannot unify the two predicates

                    // If the var doesn't start with FLOW, it means that it is a constant variable
                    // (a little ugly, I know)
                    if (!var.value.startsWith("SCOPE_")
                            && !pred2.scope.get(argi).getPossibleValueVariable().contains(var.value)) {
                        cannotUnifyBecauseConstrains = true;
                        break;
                    }

                    // We need to indicate the constrains here
                    constrainsToSuccessfullyUnify.set(argi, pred2.scope.get(argi));
                    needsConstrainsToBeInSameLiftedFamGroup = true;
                }
            }
        }

        // Clean the variables
        for (AtomVariable varBound : varsBoundByPredicateToClean) {
            varBound.value = null;
        }

        if (cannotUnifyBecauseConstrains) {
            return LIFTED_FAM_GROUP_UNIFIER.FAILED;
        }

        if (needsConstrainsToBeInSameLiftedFamGroup) {
            return LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS;
        } else {
            return LIFTED_FAM_GROUP_UNIFIER.SUCCESS;
        }
    }


/**
     * Try to unify two predicates in a lifted fam group
     * 
     * @param pred1
     * @param pred2
     * @param liftedFamGroups
     * @param constrainsToSuccessfullyUnify
     * @return
     */
    private LIFTED_FAM_GROUP_UNIFIER UnifyPredicates2(CertifiedPredicate pred1, CertifiedPredicate pred2, Candidate liftedFamGroup, Vector<Pair<ScopeVariable, ScopeVariable>> constrainsToSuccessfullyUnify) {

        // First, verify that the lifted fam group can indeed contains the predicate 1 and the
        // predicate 2.
        // If it doesn't exist, return ReturnValueLiftedFamGroup.FAILED
        LiftedFamGroupUnificateur liftedMutexGroupUnificateur = liftedFamGroupCanUnifyPredicates(pred1, pred2, liftedFamGroup);
        if (liftedMutexGroupUnificateur == null) {
            return LIFTED_FAM_GROUP_UNIFIER.FAILED;
        }

        AtomCandidate atomThatCanBeBoundWithPred1 = liftedMutexGroupUnificateur.atomWhichCanUnifyWithPred1;
        AtomCandidate atomThatCanBeBoundWithPred2 = liftedMutexGroupUnificateur.atomWhichCanUnifyWithPred2;

        HashSet<AtomVariable> varsBoundByPredicateToClean = new HashSet<AtomVariable>();
        boolean needsConstrainsToBeInSameLiftedFamGroup = false;

        // First, check if there is a constrains on this predicate which prevent the
        // unification (TODO: not very proper here, beacuse we consider that the two
        // predicate have
        // the same signature which is not always the case)
        boolean cannotUnifyBecauseConstrains = false;
        for (int argi = 0; argi < pred1.scope.size(); argi++) {
            ScopeVariable var = pred1.scope.get(argi);
            // Check if there is a constrains on this scopeVariable
            if (pred1.inputConstrainsScope.containsKey(var)
                    && pred1.inputConstrainsScope.get(var)
                            .contains(pred2.scope.get(argi))) {
                cannotUnifyBecauseConstrains = true;
                break;
            }
        }

        if (cannotUnifyBecauseConstrains) {
            return LIFTED_FAM_GROUP_UNIFIER.FAILED;
        }

        // Now try to unify those two candidates
        Map<String, ScopeVariable> tmp = new HashMap<String, ScopeVariable>();

        // First bound the 1st predicate
        for (int argi = 0; argi < pred1.scope.size(); argi++) {
            AtomVariable var = liftedFamGroup.variables.get(atomThatCanBeBoundWithPred1.paramsId.get(argi));

            // If the variable is a counted variable, it can take any value, there is no
            // need to bound
            if (var.isCountedVar) {
                continue;
            } else {

                // Here we can bound the variable with the name of the scope value.
                var.value = pred1.scope.get(argi).getUniqueName();
                varsBoundByPredicateToClean.add(var);
                tmp.put(var.value, pred1.scope.get(argi));
            } 
        }

        // Now try to unify the second predicate with those constrains
        for (int argi = 0; argi < pred2.scope.size(); argi++) {
            AtomVariable var = liftedFamGroup.variables.get(atomThatCanBeBoundWithPred2.paramsId.get(argi));

            if (var.isCountedVar) {
                continue;
            }

            else {
                String nameArgiPred2 = pred2.scope.get(argi).getUniqueName();
                // Check if the variable is correctly bound by the predicate to check
                if (var.value != null && var.value.equals(nameArgiPred2)) {
                    // It's correct here, we can continue
                    continue;
                } else {
                    // The var is bound to another value...
                    // if the var is bound to a unique value that the predicate 2 cannot take,
                    // we are sure that we cannot unify the two predicates

                    // If the var doesn't start with SCOPE_, it means that it is a constant variable
                    // (a little ugly, I know)
                    if (!var.value.startsWith("SCOPE_")
                            && !pred2.scope.get(argi).getPossibleValueVariable().contains(var.value)) {
                        cannotUnifyBecauseConstrains = true;
                        break;
                    }

                    // We need to indicate the constrains here
                    // constrainsToSuccessfullyUnify.set(argi, pred2.scope.get(argi));
                    constrainsToSuccessfullyUnify.add(Pair.of(tmp.get(var.value), pred2.scope.get(argi)));
                    needsConstrainsToBeInSameLiftedFamGroup = true;
                }
            }
        }

        // Clean the variables
        for (AtomVariable varBound : varsBoundByPredicateToClean) {
            varBound.value = null;
        }

        if (cannotUnifyBecauseConstrains) {
            return LIFTED_FAM_GROUP_UNIFIER.FAILED;
        }

        if (needsConstrainsToBeInSameLiftedFamGroup) {
            return LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS;
        } else {
            return LIFTED_FAM_GROUP_UNIFIER.SUCCESS;
        }
    }

    public void prettyDisplayResolverPrecondition() {

        for (CertifiedPredicate precondition : this.preconditionSolver.keySet()) {
            System.out.println(precondition);
            System.out.println(preconditionSolver.get(precondition));
            System.out.println("======");
        }
    }

    private LiftedFamGroupUnificateur getLiftedFamGroupWhichContainsPredicates(CertifiedPredicate pred1,
            CertifiedPredicate pred2, ArrayList<Candidate> liftedFamGroups) {

        for (Candidate liftedFamGroup : liftedFamGroups) {

            boolean canUnifyWithPred1 = false;
            boolean canUnifyWithPred2 = false;
            AtomCandidate atomWhichCanUnifyWithPred1 = null;
            AtomCandidate atomWhichCanUnifyWithPred2 = null;

            for (AtomCandidate predLiftedFamGroup : liftedFamGroup.mutexGroup) {

                if (predLiftedFamGroup.predSymbolName.equals(pred1.predicateName) && !canUnifyWithPred1) {
                    // Check if the type of each variable of the predicate correspond as well

                    for (int argi = 0; argi < pred1.scope.size(); argi++) {
                        String typeArgiPred1 = pred1.scope.get(argi).getType();
                        String typeArgiLiftedFamGroup = predLiftedFamGroup.candidateParent.variables
                                .get(predLiftedFamGroup.paramsId.get(argi)).typeName;

                        if (!typeArgiPred1.equals(typeArgiLiftedFamGroup)) {
                            break;
                        }
                        canUnifyWithPred1 = true;
                        atomWhichCanUnifyWithPred1 = predLiftedFamGroup;
                    }
                }

                if (predLiftedFamGroup.predSymbolName.equals(pred2.predicateName) && !canUnifyWithPred2) {
                    // Check if the type of each variable of the predicate correspond as well

                    for (int argi = 0; argi < pred2.scope.size(); argi++) {
                        String typeArgiPred2 = pred2.scope.get(argi).getType();
                        String typeArgiLiftedFamGroup = predLiftedFamGroup.candidateParent.variables
                                .get(predLiftedFamGroup.paramsId.get(argi)).typeName;

                        if (!typeArgiPred2.equals(typeArgiLiftedFamGroup)) {
                            break;
                        }
                        canUnifyWithPred2 = true;
                        atomWhichCanUnifyWithPred2 = predLiftedFamGroup;
                    }
                }

                if (canUnifyWithPred1 && canUnifyWithPred2) {
                    return new LiftedFamGroupUnificateur(liftedFamGroup, atomWhichCanUnifyWithPred1,
                            atomWhichCanUnifyWithPred2);
                }
            }
        }

        return null;
    }


    private LiftedFamGroupUnificateur liftedFamGroupCanUnifyPredicates(CertifiedPredicate pred1,
    CertifiedPredicate pred2, Candidate liftedFamGroup) {


        boolean canUnifyWithPred1 = false;
        boolean canUnifyWithPred2 = false;
        AtomCandidate atomWhichCanUnifyWithPred1 = null;
        AtomCandidate atomWhichCanUnifyWithPred2 = null;

        for (AtomCandidate predLiftedFamGroup : liftedFamGroup.mutexGroup) {

            if (predLiftedFamGroup.predSymbolName.equals(pred1.predicateName) && !canUnifyWithPred1) {
                // Check if the type of each variable of the predicate correspond as well

                for (int argi = 0; argi < pred1.scope.size(); argi++) {
                    String typeArgiPred1 = pred1.scope.get(argi).getType();
                    String typeArgiLiftedFamGroup = predLiftedFamGroup.candidateParent.variables
                            .get(predLiftedFamGroup.paramsId.get(argi)).typeName;

                    if (!typeArgiPred1.equals(typeArgiLiftedFamGroup)) {
                        break;
                    }
                    canUnifyWithPred1 = true;
                    atomWhichCanUnifyWithPred1 = predLiftedFamGroup;
                }
            }

            if (predLiftedFamGroup.predSymbolName.equals(pred2.predicateName) && !canUnifyWithPred2) {
                // Check if the type of each variable of the predicate correspond as well

                if (pred2.scope.size() == 0) {
                    canUnifyWithPred2 = true;
                    atomWhichCanUnifyWithPred2 = predLiftedFamGroup;
                }

                for (int argi = 0; argi < pred2.scope.size(); argi++) {
                    String typeArgiPred2 = pred2.scope.get(argi).getType();
                    String typeArgiLiftedFamGroup = predLiftedFamGroup.candidateParent.variables
                            .get(predLiftedFamGroup.paramsId.get(argi)).typeName;

                    if (!typeArgiPred2.equals(typeArgiLiftedFamGroup)) {
                        break;
                    }
                    canUnifyWithPred2 = true;
                    atomWhichCanUnifyWithPred2 = predLiftedFamGroup;
                }
            }

            if (canUnifyWithPred1 && canUnifyWithPred2) {
                return new LiftedFamGroupUnificateur(liftedFamGroup, atomWhichCanUnifyWithPred1,
                        atomWhichCanUnifyWithPred2);
            }
        }

        return null;
    }

    public void cleanAllConstrainsScope() {
        for (ArrayList<ScopeVariable> scopeVarAction : this.scopeMacroAction) {
            for (ScopeVariable scopeVar : scopeVarAction) {
                scopeVar.getConstrains().clear();
            }
        }
    }

    /**
     * Return a string containing an action in easily readable format
     * 
     * @param a       The action to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the action in easily readable format
     */
    public String prettyDisplay(Problem problem) {
        StringBuilder flowToDisplay = new StringBuilder();
        flowToDisplay.append("Flow [");

        if (methodName != null) {
            flowToDisplay.append(methodName);
            for (int i = 0; i < this.scopeMethod.size(); i++) {
                flowToDisplay.append(" arg" + i + ": " + scopeMethod.get(i));
            }
        } else {
            for (int idx_action = 0; idx_action < this.macroAction.size(); idx_action++) {
                String actionName = this.macroAction.get(idx_action);
                flowToDisplay.append(actionName);
                for (int i = 0; i < this.scopeMacroAction.get(idx_action).size(); i++) {
                    flowToDisplay.append(" arg" + i + ": " + this.scopeMacroAction.get(idx_action).get(i));
                }
                if (idx_action != this.macroAction.size() - 1) {
                    flowToDisplay.append("->");
                }
            }
        }
        flowToDisplay.append("]");

        return flowToDisplay.toString();
    }

    @Override
    public String toString() {
        StringBuilder flowToDisplay = new StringBuilder();
        flowToDisplay.append(this.getUniqueName() + " [");

        if (methodName != null) {
            flowToDisplay.append(methodName);
            for (int i = 0; i < this.scopeMethod.size(); i++) {
                flowToDisplay
                        .append(" arg" + i + ": (" + scopeMethod.get(i).getUniqueName() + ") " + scopeMethod.get(i));
            }
        } else {
            for (int idx_action = 0; idx_action < this.macroAction.size(); idx_action++) {
                String actionName = this.macroAction.get(idx_action);
                flowToDisplay.append(actionName);
                for (int i = 0; i < this.scopeMacroAction.get(idx_action).size(); i++) {
                    flowToDisplay.append(" " + this.scopeMacroAction.get(idx_action).get(i));
                }
                if (idx_action != this.macroAction.size() - 1) {
                    flowToDisplay.append("->");
                }
            }
        }
        flowToDisplay.append("]");

        return flowToDisplay.toString();
    }

    public String getUniqueName() {
        StringBuilder uniqueFlowName = new StringBuilder();
        uniqueFlowName.append("FLOW_");
        if (this.methodName != null) {
            uniqueFlowName.append(this.methodName);
        } else {
            for (int idx_action = 0; idx_action < this.macroAction.size(); idx_action++) {
                String actionName = this.macroAction.get(idx_action);
                uniqueFlowName.append(actionName);
                if (idx_action != this.macroAction.size() - 1) {
                    uniqueFlowName.append("->");
                }
            }
        }

        uniqueFlowName.append("_" + uniqueId);

        return uniqueFlowName.toString();
    }
}

class ReturnValueLiftedFamGroup {
    LIFTED_FAM_GROUP_UNIFIER result;
    CertifiedPredicate predWhichCanUnifyWith;

    public ReturnValueLiftedFamGroup(LIFTED_FAM_GROUP_UNIFIER result, CertifiedPredicate pred) {
        this.result = result;
        this.predWhichCanUnifyWith = pred;
    }
}

class LiftedFamGroupUnificateur {
    Candidate liftedFamGroup;
    AtomCandidate atomWhichCanUnifyWithPred1;
    AtomCandidate atomWhichCanUnifyWithPred2;

    public LiftedFamGroupUnificateur(Candidate liftedFamGroup, AtomCandidate predicateWhichCanUnifyWithPred1,
            AtomCandidate predicateWhichCanUnifyWithPred2) {
        this.liftedFamGroup = liftedFamGroup;
        this.atomWhichCanUnifyWithPred1 = predicateWhichCanUnifyWithPred1;
        this.atomWhichCanUnifyWithPred2 = predicateWhichCanUnifyWithPred2;
    }
}

class SolverPrecondition {

    boolean isStaticPrecondition;
    boolean mustCheckInitValue;
    boolean isInvariantTrue;
    HashSet<ScopeVariable> constrainsOnScope;
    HashSet<Triple<HashSet<LiftedFlow>, ScopeVariable, ScopeVariable>> scopeVarThatMustBeEquals;
    HashSet<LiftedFlow> trueIfPassingByThoseFLows;

    public SolverPrecondition() {
        this.isStaticPrecondition = false;
        this.mustCheckInitValue = false;
        this.isInvariantTrue = false;
        this.scopeVarThatMustBeEquals = new HashSet<Triple<HashSet<LiftedFlow>, ScopeVariable, ScopeVariable>>();
        this.constrainsOnScope = new HashSet<ScopeVariable>();
        this.trueIfPassingByThoseFLows = new HashSet<LiftedFlow>();
    }

    @Override
    public String toString() {
        StringBuilder solverPrecondition = new StringBuilder();

        solverPrecondition.append("Precondition is static: " + isStaticPrecondition + "\n");
        solverPrecondition.append("Precondition is invariantTrue: " + isInvariantTrue + "\n");
        solverPrecondition.append("Must check init value: " + mustCheckInitValue + "\n");
        solverPrecondition.append("Constrains with the scopes: " + constrainsOnScope + "\n");
        solverPrecondition.append("Scope var that must be equals:\n");
        for (Triple<HashSet<LiftedFlow>, ScopeVariable, ScopeVariable> scopeVarThatMustBeEqual : this.scopeVarThatMustBeEquals) {
            solverPrecondition.append("(" + scopeVarThatMustBeEqual.getMiddle().getUniqueName() + "="
                    + scopeVarThatMustBeEqual.getRight().getUniqueName() + ") \n");
        }

        return solverPrecondition.toString();
    }
}
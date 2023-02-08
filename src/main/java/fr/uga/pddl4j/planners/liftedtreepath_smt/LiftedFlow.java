package fr.uga.pddl4j.planners.liftedtreepath_smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.SAS_Plus.AtomCandidate;
import fr.uga.pddl4j.parser.SAS_Plus.AtomVariable;
import fr.uga.pddl4j.parser.SAS_Plus.Candidate;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import org.apache.commons.lang3.tuple.Pair;

public class LiftedFlow {

    static int numberLiftedFlow = 0;

    public int uniqueId;
    private Method method = null;
    private String methodName = null;
    private ArrayList<String> macroAction = null;

    LiftedFlow parentFlow = null;
    private Integer parentId; // ID of task for method, ID of method for action
    HashSet<LiftedFlow> nextsFlow;
    HashSet<LiftedFlow> previousesFlow;

    Expression<String> preconditions;
    Expression<String> effects;

    private ArrayList<ScopeVariable> scopeMethod;
    private ArrayList<ArrayList<ScopeVariable>> scopeMacroAction;

    HashSet<CertifiedPredicate> inputCertifiedPredicates;
    HashSet<CertifiedPredicate> outputCertifiedPredicates;
    HashSet<CertifiedPredicate> preconditionPredicates;

    Map<CertifiedPredicate, SolverPrecondition> preconditionSolver;

    boolean isPrimitiveFlow;
    int numberChildrenPrimitiveFlow;

    public LiftedFlow(String methodName, LiftedFlow parentFlow, Integer parentTaskId,
            ArrayList<ScopeVariable> methodScope) {
        this.methodName = methodName;
        this.parentFlow = parentFlow;
        this.parentId = parentTaskId;
        this.scopeMethod = methodScope;
        isPrimitiveFlow = false;
        this.numberChildrenPrimitiveFlow = 0;

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.uniqueId = LiftedFlow.numberLiftedFlow;
        LiftedFlow.numberLiftedFlow++;
    }

    public LiftedFlow(ArrayList<String> macroAction, LiftedFlow parentFlow,
            ArrayList<ArrayList<ScopeVariable>> scopeMacroAction, Map<String, ParsedAction> actionNameToObject) {
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

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.inputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.outputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.preconditionPredicates = new HashSet<CertifiedPredicate>();

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

    public void computePredicatesFromPreconditions() {

        int numberPreActions = this.preconditions.getChildren().size();
        if (numberPreActions == 0 && this.preconditions.getSymbol() != null) {
            numberPreActions = 1;
        }

        for (int preId = 0; preId < numberPreActions; preId++) {

            Expression<String> pre;

            if (numberPreActions > 1) {
                pre = this.preconditions.getChildren().get(preId);
            } else {
                pre = this.preconditions;
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
                scopePred.add(this.scopeMacroAction.get(0).get(idxArg));
            }

            // TODO what to do for negative input certified predicate ?? Add them or
            // not add them (and consider all predicate which are not here as invariant
            // false ?)
            // Nope, we have to consider with the SAS+ to see if those canidate can have
            // multiple values
            CertifiedPredicate certPredicate = new CertifiedPredicate(namePredicate, predicateIsPositive,
                    scopePred, this);

            this.preconditionPredicates.add(certPredicate);
        }
    }

   

    public void computeOutputCertifiedPredicates(HashSet<String> staticPredicates, HashSet<Candidate> liftedFamGroups) {

        // First add the effects of the actions as they are the kings here
        // (the most recent information we have about the states of the predicates)

        int numberEffActions = this.effects.getChildren().size();
        if (numberEffActions == 0 && this.effects.getSymbol() != null) {
            numberEffActions = 1;
        }

        HashSet<CertifiedPredicate> negativeEffs = new HashSet<>();

        for (int effId = 0; effId < numberEffActions; effId++) {

            Expression<String> eff;
            if (numberEffActions > 1) {
                eff = this.effects.getChildren().get(effId);
            } else {
                eff = this.effects;
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

            // If it is a static predicate do not put it as effect as the action
            if (staticPredicates.contains(namePredicate)) {
                continue;
            }

            ArrayList<ScopeVariable> scopePred = new ArrayList<ScopeVariable>();

            for (Symbol<String> arg : eff.getArguments()) {
                int idxArg = Integer.parseInt(arg.getValue().substring(2));
                scopePred.add(this.scopeMacroAction.get(0).get(idxArg));
            }

            // Create the effect as a certified predicate
            CertifiedPredicate certifiedPred = new CertifiedPredicate(namePredicate, predicateIsPositive, scopePred,
                    this);

            if (!predicateIsPositive) {
                negativeEffs.add(certifiedPred);
                continue;
            }

            // Now we can add the effect (Question do we add negative predicate or do we
            // cansider
            // all predicate which are not among the positive predicate as false ?)
            this.outputCertifiedPredicates.add(certifiedPred);
        }

        // Check if we can remove some predicates from effects with SAS+
        // (for exemple, if we have [at SCOPE_0 SCOPE_1] and [not at SCOPE_0 SCOPE_2]
        // and we have {at C0: vehicule C1: location} in LiftedFamGroup
        // then, we only need the predicate [at SCOPE_0 SCOPE_1] to totally describe the
        // state...

        // Now add all the negative effects only if there is no the opposite predicate already in the precondition
        // FOR NOW, DO NOT ADD NEGATIVE EFFECTS 
        // for (CertifiedPredicate negativeEff : negativeEffs) {
        //     boolean oppositePredIsInEffect = false;
        //     for (CertifiedPredicate precondition : this.preconditionPredicates) {
        //         if (precondition.isOppositeTo(negativeEff)) {
        //             oppositePredIsInEffect = true;
        //             break;
        //         }
        //     }
        //     if (!oppositePredIsInEffect) {
        //         this.outputCertifiedPredicates.add(negativeEff);
        //     }
        // }

        // Now add all precondition only if this is not a static precondition and the effect has not removed this precondition
        for (CertifiedPredicate precondition : this.preconditionPredicates) {
            if (staticPredicates.contains(precondition.predicateName)) {
                continue;
            }
            boolean oppositePredIsInEffect = false;
            for (CertifiedPredicate certifiedEff : this.outputCertifiedPredicates) {
                if (certifiedEff.isOppositeTo(precondition)) {
                    oppositePredIsInEffect = true;
                    break;
                }
            }
            for (CertifiedPredicate negEff : negativeEffs) {
                if (negEff.isOppositeTo(precondition)) {
                    oppositePredIsInEffect = true;
                    break;
                }
            }
            if (!oppositePredIsInEffect) {
                this.outputCertifiedPredicates.add(precondition);
            }
        }

        HashSet<CertifiedPredicate> inputCertifiedPredThatMustBeTransmit = new HashSet<>();

        // Now for each certified input, we only add it if we do not already certified it
        for (CertifiedPredicate inputCertifiedPred : this.inputCertifiedPredicates) {

            boolean canBePruned = false;
            
            // Check if this certified predicate can be unified with one of our output certificate
            for (CertifiedPredicate outpuCertifiedPredicate : this.outputCertifiedPredicates) {
                
                // Initialize an array of constrains which will indicate which contrains should
                // be filled
                // for the two predicate to be in the same lifted fam group
                ArrayList<ScopeVariable> constrainsToBeInSameLiftedFamGroup = new ArrayList<ScopeVariable>();
                for (int i = 0; i < inputCertifiedPred.scope.size(); i++) {
                    constrainsToBeInSameLiftedFamGroup.add(null);
                }

                LIFTED_FAM_GROUP_UNIFIER resultUnification = UnifyPredicates(inputCertifiedPred, outpuCertifiedPredicate, liftedFamGroups, constrainsToBeInSameLiftedFamGroup);

                if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
                    // We can prune this predicate
                    canBePruned = true;
                    break;
                }
                else if (resultUnification == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {
                    // We have to add those constrains 
                    for (int i = 0; i < constrainsToBeInSameLiftedFamGroup.size(); i++) {
                        if (constrainsToBeInSameLiftedFamGroup.get(i) != null) {
                            inputCertifiedPred.addOutputConstrains(inputCertifiedPred.scope.get(i), constrainsToBeInSameLiftedFamGroup.get(i));
                        }
                    }
                    int ici = 0;
                }
            }

            if (!canBePruned) {
                inputCertifiedPredThatMustBeTransmit.add(inputCertifiedPred);
            }
        }


        this.outputCertifiedPredicates.addAll(inputCertifiedPredThatMustBeTransmit);

        // Finally add all the input certified predicates (only if we NEED TO
        // describe this effect. e.g: is we have a [at SCOPE_0 SCOPE_1] and we already
        // have a [at SCOPE_0 SCOPE_5]
        // in action effect, and we have {at C0: vehicule C1: location} in
        // LiftedFamGroup. Then we do not have to
        // add this ceritfied predicate as effect)
        // addCertifiedCandidateInOutputEffectIfNotInMutexGroup(this.inputCertifiedPredicates, liftedFamGroups,
        //         staticPredicates, true);

        // int a = 0;
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

    public void addCertifiedCandidateInOutputEffectIfNotInMutexGroup(HashSet<CertifiedPredicate> predsToAdd,
            HashSet<Candidate> liftedFamGroups, HashSet<String> staticPredicates,
            boolean addConstrainsOnScopeIfCanUnifyWithConstrains) {

        for (CertifiedPredicate predToAdd : predsToAdd) {

            if (staticPredicates.contains(predToAdd.predicateName)) {
                continue;
            }

            // First check if we already have this predicate. if so, no need to re add it
            for (CertifiedPredicate outputPred : this.outputCertifiedPredicates) {
                if (outputPred.predicateName.equals(predToAdd.predicateName)
                        && outputPred.scope.equals(predToAdd.scope)) {
                    continue;
                }
            }

            boolean canBePruned = false;

            // Check if this predicate is into a liftedFam
            for (Candidate liftedFamGroup : liftedFamGroups) {
                for (AtomCandidate atomCandidate : liftedFamGroup.mutexGroup) {
                    if (atomCandidate.predSymbolName.equals(predToAdd.predicateName)) {

                        boolean canBeRepresentedByLiftedFamGroup = true;
                        // Check if the type of each arg is also identical
                        for (int argi = 0; argi < predToAdd.scope.size(); argi++) {
                            if (!atomCandidate.candidateParent.variables.get(atomCandidate.paramsId.get(argi)).typeName
                                    .equals(predToAdd.scope.get(argi).getType())) {
                                canBeRepresentedByLiftedFamGroup = false;
                                break;
                            }
                        }
                        if (!canBeRepresentedByLiftedFamGroup) {
                            continue;
                        }

                        if (addConstrainsOnScopeIfCanUnifyWithConstrains) {
                            // Create our array of constrains
                            ArrayList<ScopeVariable> constrainsToBeFilledToSuccessfullyUnify = new ArrayList<ScopeVariable>();
                            for (int i = 0; i < predToAdd.scope.size(); i++) {
                                constrainsToBeFilledToSuccessfullyUnify.add(null);
                            }

                            ReturnValueLiftedFamGroup retValueLiftedFamGroup = predicateIsInSameLiftedFamGroupAsOutputPred(
                                    predToAdd, liftedFamGroup, atomCandidate, constrainsToBeFilledToSuccessfullyUnify,
                                    false);

                            if (retValueLiftedFamGroup.result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS) {
                                canBePruned = true;
                                break;
                            } else if (retValueLiftedFamGroup.result == LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS) {
                                // Add the constrains here, the pred to add can only be true
                                // if it doesn't violate the constrains

                                for (int argi = 0; argi < predToAdd.scope.size(); argi++) {
                                    if (constrainsToBeFilledToSuccessfullyUnify.get(argi) != null) {

                                        // Check if we have a contrains that prevent this predicate to be true
                                        // if (predToAdd.inputConstrainsScope.containsKey(predToAdd.scope.get(argi)) &&
                                        // predToAdd.inputConstrainsScope.get(predToAdd.scope.get(argi)).contains(retValueLiftedFamGroup.predWhichCanUnifyWith.scope.get(argi)))
                                        // {
                                        // continue;
                                        // }

                                        if (!predToAdd.outputConstrainsScope.containsKey(predToAdd.scope.get(argi))) {
                                            predToAdd.outputConstrainsScope.put(predToAdd.scope.get(argi),
                                                    new HashSet<>());
                                        }
                                        predToAdd.outputConstrainsScope.get(predToAdd.scope.get(argi))
                                                .add(constrainsToBeFilledToSuccessfullyUnify.get(argi));
                                    }
                                }

                                // predToAdd.constrainsScope.put(null, null)
                                canBePruned = false;
                            }
                            int a = 0;
                        } else {
                            // Check if a predicate in the effect already SAS+ this effect
                            canBePruned = predicateCanBeSASPlusPruned(predToAdd, liftedFamGroup, atomCandidate);
                            break;
                        }

                    }
                }
                if (canBePruned) {
                    break;
                }
            }

            if (!canBePruned) {
                // We can add this candidate into our output effects
                this.outputCertifiedPredicates.add(predToAdd);
            }
        }
    }
    
    public void determinateHowToResolvePreconditions(HashSet<String> staticPredicates,
            HashSet<Candidate> liftedFamGroups) {

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
                LIFTED_FAM_GROUP_UNIFIER resultUnification = UnifyPredicates(precondition, inputCertifiedPredicate, liftedFamGroups, constrainsToBeInSameLiftedFamGroup);

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

                    if (inputCertifiedPredicate.certifiers.contains(this)) {
                        // It means that we are confirming this precondition with our input certificate,
                        // this precondition should ne be checked
                        // It can only be true is all argument are identical
                        boolean allScopeVarAreIdentical = true;
                        for (int argi = 0; argi < precondition.scope.size(); argi++) {
                            String val1 = precondition.scope.get(argi).getUniqueName();
                            String val2 = inputCertifiedPredicate.scope.get(argi).getUniqueName();
                            if (!val1.equals(val2)) {
                                allScopeVarAreIdentical = false;
                                // Those two must be equals
                                solverPrecondition.scopeVarThatMustBeEquals.add(Pair.of(precondition.scope.get(argi), inputCertifiedPredicate.scope.get(argi)));
                            }
                        }

                        if (allScopeVarAreIdentical) {
                            solverPrecondition.isInvariantTrue = true;
                        }

                        shouldCheckInitialPred = false;
                    } else {
                        System.out.println("PATH NOT IMPLEMENTED ! ");
                        System.exit(1);
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

                            for (int i = 0; i < inputCertifiedPredicate.scope.size(); i++) {
                                if (i != argi) {
                                    // TODO, we have to add the constrains of the inputCertifiedPredicate here !!!
                                    // precondition.scope.get(argi).addConstrains(pivotConstrain,
                                    //         precondition.scope.get(i),
                                    //         inputCertifiedPredicate.scope.get(i), this);

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
            HashSet<Candidate> liftedFamGroups, ArrayList<ScopeVariable> constrainsToSuccessfullyUnify) {

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
        // unification (TODO: not very proper here, beacuse we consider that the two predicate have
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


                    // If the var doesn't start with FLOW, it means that it is a constant variable (a little ugly, I know)
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
        } 
        else {
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
            CertifiedPredicate pred2, HashSet<Candidate> liftedFamGroups) {

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


    public void cleanAllConstrainsScope() {
        for (ScopeVariable scopeVar : this.scopeMacroAction.get(0)) {
            scopeVar.getConstrains().clear();
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
    HashSet<Pair<ScopeVariable, ScopeVariable>> scopeVarThatMustBeEquals;

    public SolverPrecondition() {
        this.isStaticPrecondition = false;
        this.mustCheckInitValue = false;
        this.isInvariantTrue = false;
        this.scopeVarThatMustBeEquals = new HashSet<Pair<ScopeVariable, ScopeVariable>>();
        this.constrainsOnScope = new HashSet<ScopeVariable>();
    }

    @Override
    public String toString() {
        StringBuilder solverPrecondition = new StringBuilder();

        solverPrecondition.append("Precondition is static: " + isStaticPrecondition + "\n");
        solverPrecondition.append("Precondition is invariantTrue: " + isInvariantTrue + "\n");
        solverPrecondition.append("Must check init value: " + mustCheckInitValue + "\n");
        solverPrecondition.append("Constrains with the scopes: " + constrainsOnScope + "\n");
        solverPrecondition.append("Scope var that must be equals:\n");
        for (Pair<ScopeVariable, ScopeVariable> scopeVarThatMustBeEqual : this.scopeVarThatMustBeEquals) {
            solverPrecondition.append("(" + scopeVarThatMustBeEqual.getLeft().getUniqueName() + "="
                    + scopeVarThatMustBeEqual.getRight().getUniqueName() + ") \n");
        }

        return solverPrecondition.toString();
    }
}
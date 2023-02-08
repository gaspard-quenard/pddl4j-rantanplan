package fr.uga.pddl4j.planners.liftedtreepath_smt;

import java.util.Vector;

import javax.lang.model.element.Element;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;
import org.apache.logging.log4j.core.LifeCycle;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.SocketException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import fr.uga.pddl4j.util.BitVector;
import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.NamedTypedList;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.ParsedMethod;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.TypedSymbol;
import fr.uga.pddl4j.parser.SAS_Plus.AtomCandidate;
import fr.uga.pddl4j.parser.SAS_Plus.AtomVariable;
import fr.uga.pddl4j.parser.SAS_Plus.Candidate;
import fr.uga.pddl4j.parser.SAS_Plus.SASPlusGeneratorDomain;
import fr.uga.pddl4j.parser.SAS_Plus.SASplusLiftedFamGroup;
import fr.uga.pddl4j.parser.SAS_Plus.Strips2SasPlus;
import fr.uga.pddl4j.plan.Hierarchy;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;

enum LIFTED_FAM_GROUP_UNIFIER {
    SUCCESS,
    FAILED,
    SUCCESS_WITH_CONSTRAINS
}

public class LiftedTreePathEncoder {

    private final Problem problem;

    StringBuilder allClauses;
    Vector<String> allBoolVariables;
    Vector<String> allIntVariables;

    HashSet<LiftedFlow> initialPaths;
    HashSet<LiftedFlow> paths;

    HashSet<String> staticPredicates;

    Map<String, Vector<String>> dictTypeToObjects;
    Map<String, Integer> liftedMethodToNumberSubtasks;

    Map<String, ParsedMethod> methodNameToObj;
    Map<String, ParsedAction> actionNameToObj;

    Map<String, Integer> objNameToUniqueId;

    private int layer = 0;

    String filenameSMT = "LiftedTreePath.SMT";
    private String path_exec_VAL = "src/test/resources/validators/pandaPIparser";
    String domainPath;
    String problemPath;

    // A dictionary which map the name of an object to the type of the object
    private Map<String, String> dictObjNameToType;

    Map<String, HashSet<String>> dictPredNameToLiftedActionWithPredAsPosEff;
    Map<String, HashSet<String>> dictPredNameToLiftedActionWithPredAsNegEff;

    Map<String, Map<String, ArrayList<Integer>>> dictIdxArgPredToIdxArgActionAssociatedPosEff;
    Map<String, Map<String, ArrayList<Integer>>> dictIdxArgPredToIdxArgActionAssociatedNegEff;

    PrimitiveTree primitiveTree;

    HashSet<Candidate> liftedFamGroups;

    public void showAllPaths() {

        // Show a single path
        for (LiftedFlow f : this.initialPaths) {
            String prettyDisplayLiftedFlow = f.prettyDisplay(problem);
            System.out.println(prettyDisplayLiftedFlow);
        }
    }

    public LiftedTreePathEncoder(Problem problem, String domainPath, String problemPath) {

        this.domainPath = domainPath;
        this.problemPath = problemPath;

        this.problem = problem;
        this.allBoolVariables = new Vector<String>();
        this.allIntVariables = new Vector<String>();
        this.allClauses = new StringBuilder();
        this.primitiveTree = new PrimitiveTree();

        this.initialPaths = new HashSet<LiftedFlow>();
        this.paths = new HashSet<LiftedFlow>();
        // Ok, let's begin !
        int previousTaksId = -1;

        preprocessing();

        // Get SAS+ cliques (in the lifted form)
        SASplusLiftedFamGroup.determinateLiftedFamGroups(problem);
        this.liftedFamGroups = SASplusLiftedFamGroup.candidatesProved;

        for (int i = 0; i < this.problem.getInitialTaskNetwork().getTasks().size(); i++) {

            int idxTaskNetwork = this.problem.getInitialTaskNetwork().getTasks().get(i);

            // Get all the methods which can resolve this task and the scope of the variable
            // of each of the method which can resolve this task

            Map<String, ArrayList<ScopeVariable>> methodNameToScope = new HashMap<String, ArrayList<ScopeVariable>>();
            for (int idxMethod : this.problem.getTaskResolvers().get(idxTaskNetwork)) {
                Method m = this.problem.getMethods().get(idxMethod);
                if (!methodNameToScope.containsKey(m.getName())) {
                    // Initialize the score of this method
                    ArrayList<ScopeVariable> scopeMethod = new ArrayList<>();
                    for (int k = 0; k < m.getParameters().length; k++) {
                        scopeMethod.add(new ScopeVariable());
                    }
                    methodNameToScope.put(m.getName(), scopeMethod);
                }
                // Add all the arguments in the scope of the method
                ArrayList<ScopeVariable> scopeMethod = methodNameToScope.get(m.getName());
                for (int argi = 0; argi < m.getParameters().length; argi++) {
                    String objName = problem.getConstantSymbols().get(m.getInstantiations()[argi]);
                    String objType = this.dictObjNameToType.get(objName);
                    scopeMethod.get(argi).addValueToScope(objName);
                    // Add the type as well
                    scopeMethod.get(argi).addTypeVariable(objType);
                }
            }

            // Now we can add all of our methods with the appropriate scope
            // Create a flow for each different method that can be taken
            for (String methodName : methodNameToScope.keySet()) {
                LiftedFlow f = new LiftedFlow(methodName, null, idxTaskNetwork, methodNameToScope.get(methodName));
                this.paths.add(f);

                if (i == 0) {
                    this.initialPaths.add(f);
                }

                // Indicate to all the flows from the previous task network that they we must
                // follow them
                for (LiftedFlow previousLiftedFlow : this.paths) {
                    if (previousLiftedFlow.getParentId() == previousTaksId) {
                        previousLiftedFlow.addNextLiftedFlow(f);

                        f.addPreviousesLiftedFlow(previousLiftedFlow);
                    }
                }
            }
            previousTaksId = idxTaskNetwork;
        }

        showAllPaths();

        // Now, we have all our initial paths
        int layerMax = 10;
        while (layer <= layerMax) {

            System.out.println("==================");
            System.out.println("FOR LAYER: " + layer);
            System.out.println("==================");

            // Check if there exist a path where there are only primitivate action
            // If there is, encode all paths with primitive actions to SAT (and encode
            // all the paths possible as well to better guide the SAT research)

            // System.out.println("Get all primitive paths");
            // getAllPrimitivePaths();

            System.out.println("Create primitive tree");
            // createPrimitiveTree();
            createPrimitiveTreeQuick();

            boolean primitivePathExist = (this.primitiveTree.nodes.size() > 0);

            if (primitivePathExist) {

                // Find all the certified predicate (predicate which we do know the value if we
                // are in a current node)
                System.out.println("Compute certified predicates primitive tree");
                computeCertifiedPredicatesPrimitiveTree();

                System.out.println("Encode SMT\n");
                // Encode for SAT
                // CleanAndOptimizePritmitivePaths();
                try {
                    encodeSAT();
                } catch (IOException e) {
                    // Handle the exception
                    e.printStackTrace();
                }

                // Run the SMT solver on the file
                String responseSMT = executeSMTSolverOnFile();  
                
                if (fileIsSatisfiable(responseSMT)) {
                    System.out.println("SAT solution found !");

                    System.out.println("Extract the hierarchy of the plan...\n");
                    SequentialPlan plan = extractPlanAndHierarchyFromSolver(responseSMT);
        
                    // Verify if the plan is valid
                    System.out.println("Check if plan is valid...");
                    boolean planIsValid;
                    try {
                        planIsValid = validatePlan(problem, plan);
                    } catch (IOException e) {
                        System.out.println("Failed to check if plan is valid !\n");
                        planIsValid = false;
                    }
        
                    if (planIsValid) {
                        System.out.println("Plan is valid !\n");
                    } else {
                        System.out.println("Plan is NOT valid !\n");
                    }

                    System.out.println("Finishing executing at layer: " + this.layer);

                    return;
                }
            }

            // Refine each method in all the flows
            System.out.println("Number flows before refining: " + this.paths.size());
            refineAllLiftedFlows();
            System.out.println("Number flows after refining: " + this.paths.size());


            // Remove all paths which are impossible
            // (e.g: Initial path with an action flow impossible)
            // or an flow which cannot be possible if a previous action flow is executed
            // cleanAllLiftedFlows();

            this.layer++;
        }

        System.out.println("Finishing executing at layer: " + this.layer);
    }

    private void refineAllLiftedFlows() {

        HashSet<LiftedFlow> newPaths = new HashSet<LiftedFlow>();
        HashSet<LiftedFlow> newInitialPaths = new HashSet<LiftedFlow>();

        Map<LiftedFlow, HashSet<LiftedFlow>> dictMethodFlowToAllFirstChildrenFlows = new HashMap<LiftedFlow, HashSet<LiftedFlow>>();

        // Iterate over all flows
        for (LiftedFlow flowParent : this.paths) {

            // We do not refine the action flow (it is already refined to maximum)
            if (!flowParent.isMethodLiftedFlow()) {
                newPaths.add(flowParent);
                if (flowParent.getPreviousesLiftedFlow().size() == 0) {
                    newInitialPaths.add(flowParent);
                }
                continue;
            }

            // Iterate over all children of the method of this flow
            String methodNameFlow = flowParent.getMethodName();

            // System.out.println("Refine flow : " + flowParent);

            ArrayList<String> consecutiveActionsOfLiftedFlow = new ArrayList<String>();
            ArrayList<ArrayList<ScopeVariable>> consecutiveActionsOfLiftedFlowScope = new ArrayList<ArrayList<ScopeVariable>>();
            boolean lastSubTaskIsAction = false;
            HashSet<LiftedFlow> previousLiftedFlows = new HashSet<LiftedFlow>();
            HashSet<LiftedFlow> newLiftedFlows = new HashSet<LiftedFlow>();
            boolean firstNewLiftedFlow = true;
            boolean subTaskIsPrimitive = false;

            ParsedMethod liftedMethod = this.methodNameToObj.get(methodNameFlow);

            // Iterate over all subtasks of this method
            for (int idxSubtask = 0; idxSubtask < liftedMethod.getSubTasks().getChildren().size(); idxSubtask++) {

                Expression<String> subtask = liftedMethod.getSubTasks().getChildren().get(idxSubtask);
                // Check if the subtasks is an action (primitive task or another task)

                String subtaskName = subtask.getSymbol().getValue();

                subTaskIsPrimitive = this.actionNameToObj.keySet().contains(subtaskName);

                if (subTaskIsPrimitive) {
                    // This is an action. Get the action object associated with this
                    // Initialize the action with the correct scope
                    lastSubTaskIsAction = true;

                    // Find the scope of the action (two cases here:
                    // - first: it heritate its scope from a parent method (then we use the same
                    // scope as the parent method))
                    // - two: it is a constant variable (then we create a new scope with only the
                    // constant variable)
                    ArrayList<ScopeVariable> scopeAction = new ArrayList<>();
                    for (int argi = 0; argi < subtask.getArguments().size(); argi++) {
                        String nameArg = subtask.getArguments().get(argi).getValue();
                        try {
                            int idxArgOfMethod = Integer.parseInt(nameArg.substring(2));
                            scopeAction.add(flowParent.getScopeVariables().get(idxArgOfMethod));
                        } catch (Exception e) {
                            // Maybe it is a constant variable
                            // TODO create a scope variable for each constant to avoir duplicatas
                            // FOR NOW DO NOT DO IT
                            // scopeAction.add(nameArg);
                            System.out.println("WE WILL SEE THAT LATER...");
                            System.exit(1);
                        }
                    }

                    consecutiveActionsOfLiftedFlow.add(subtaskName);
                    consecutiveActionsOfLiftedFlowScope.add(scopeAction);
                    if (idxSubtask != liftedMethod.getSubTasks().getChildren().size() - 1) {
                        continue;
                    }
                }

                if (lastSubTaskIsAction) {
                    // Create a new flow with all these actions in it
                    LiftedFlow flowAction = new LiftedFlow(consecutiveActionsOfLiftedFlow, flowParent,
                            consecutiveActionsOfLiftedFlowScope, actionNameToObj);
                    consecutiveActionsOfLiftedFlow = new ArrayList<String>();
                    consecutiveActionsOfLiftedFlowScope = new ArrayList<ArrayList<ScopeVariable>>();
                    lastSubTaskIsAction = false;
                    newLiftedFlows.add(flowAction);
                }

                if (!subTaskIsPrimitive) {
                    // First, we need to know the scope of each argument of this subtask
                    ArrayList<ScopeVariable> scopeSubtask = new ArrayList<ScopeVariable>();
                    for (int argi = 0; argi < subtask.getArguments().size(); argi++) {
                        String nameArg = subtask.getArguments().get(argi).getValue();
                        try {
                            int idxArgOfMethod = Integer.parseInt(nameArg.substring(2));
                            scopeSubtask.add(flowParent.getScopeVariables().get(idxArgOfMethod));
                        } catch (Exception e) {
                            // Maybe it is a constant variable
                            // scopeSubtask.add(nameArg);
                            System.out.println("WE WILL SEE THAT LATER...");
                            System.exit(1);
                        }
                    }

                    // Now, we need to find all the methods which can solve this subtask
                    for (ParsedMethod subMethod : problem.getParsedProblem().getMethods()) {

                        String subMethodName = subMethod.getName().getValue();
                        ArrayList<ScopeVariable> scopeSubMethod = new ArrayList<ScopeVariable>();

                        // If this method cannot resolve this subtask, continue
                        if (!subMethod.getTask().getSymbol().getValue().equals(subtaskName)) {
                            continue;
                        }

                        // Here it where it is delicate, when this method use a parameter of the task
                        // parent, use the scope of the task
                        // parent. Else, initialize a new scope with all possible value in it (maybe it
                        // is not optimal, I don't know there)

                        // First, we need to know with which argument the parent method called the task

                        // Iterate over all argument of the subMethod
                        for (TypedSymbol<String> subMethodArg : subMethod.getParameters()) {
                            // Find if this is also a parameter of the parent task
                            String nameParameter = subMethodArg.getValue();
                            int idxArgOfMethod = Integer.parseInt(nameParameter.substring(2));

                            // Check if it is a parameter of the parent task
                            boolean isParameterOfParentTask = false;
                            for (int i_parentTaskParam = 0; i_parentTaskParam < subMethod.getTask().getArguments()
                                    .size(); i_parentTaskParam++) {
                                if (subMethod.getTask().getArguments().get(i_parentTaskParam).getValue()
                                        .equals(nameParameter)) {
                                    // Use the scope of the parent task
                                    scopeSubMethod.add(scopeSubtask.get(i_parentTaskParam));
                                    isParameterOfParentTask = true;
                                    break;
                                }
                            }

                            // Or if it is a new parameter introduced by the method
                            if (!isParameterOfParentTask) {
                                ScopeVariable scopeArg = new ScopeVariable();
                                // Get the type of the argument
                                String typeArg = subMethodArg.getTypes().get(0).getValue();
                                scopeArg.addTypeVariable(typeArg);
                                // Initialize the scope argument with all value of this type
                                for (String obj : dictTypeToObjects.get(typeArg)) {
                                    scopeArg.addValueToScope(obj);
                                }
                                scopeSubMethod.add(scopeArg);
                            }
                        }

                        LiftedFlow flowMethod = new LiftedFlow(subMethodName, flowParent, 0, scopeSubMethod);
                        newLiftedFlows.add(flowMethod);
                    }
                }

                if (firstNewLiftedFlow) {
                    // HashSet<LiftedFlow> allChild
                    dictMethodFlowToAllFirstChildrenFlows.put(flowParent, newLiftedFlows);
                    // for (LiftedFlow newLiftedFlow : newLiftedFlows) {
                    //     for (LiftedFlow previousLiftedFlowParentMethod : flowParent.getPreviousesLiftedFlow()) {
                    //         newLiftedFlow.addNextLiftedFlow(previousLiftedFlowParentMethod);
                    //     }
                    // }
                    firstNewLiftedFlow = false;
                }

                if (idxSubtask == liftedMethod.getSubTasks().getChildren().size() - 1) {
                    for (LiftedFlow newLiftedFlow : newLiftedFlows) {
                        for (LiftedFlow nextLiftedFlowParentMethod : flowParent.getNextsLiftedFlow()) {
                            newLiftedFlow.addNextLiftedFlow(nextLiftedFlowParentMethod);
                        }
                    }
                }

                // This flow method should follow the previous flow method
                for (LiftedFlow previousLiftedFlow : previousLiftedFlows) {
                    for (LiftedFlow nextLiftedFlow : newLiftedFlows) {
                        previousLiftedFlow.addNextLiftedFlow(nextLiftedFlow);
                        nextLiftedFlow.addPreviousesLiftedFlow(previousLiftedFlow);
                    }
                }

                // Add all newLiftedFlows to the path
                newPaths.addAll(newLiftedFlows);

                if (flowParent.getPreviousesLiftedFlow().size() == 0 && idxSubtask == 0) {
                    newInitialPaths.addAll(newLiftedFlows);
                }

                // System.out.println("Subtask: " + idxSubtask + " ");
                // for (LiftedFlow newLiftedFlow : newLiftedFlows) {
                //     System.out.println(newLiftedFlow);
                // }
                // System.out.println("===============");

                previousLiftedFlows = newLiftedFlows;
                newLiftedFlows = new HashSet<LiftedFlow>();
            }

            int a = 0;
        }

        // Not optimal at all, but since we are lifted, we do not care ?
        for (LiftedFlow newLiftedFlow : newPaths) {
            for (LiftedFlow oldParentFlow : dictMethodFlowToAllFirstChildrenFlows.keySet()) {
                if (newLiftedFlow.getPreviousesLiftedFlow().contains(oldParentFlow)) {
                    newLiftedFlow.getPreviousesLiftedFlow().remove(oldParentFlow);
                }
                if (newLiftedFlow.getNextsLiftedFlow().contains(oldParentFlow)) {
                    newLiftedFlow.getNextsLiftedFlow().remove(oldParentFlow);
                    newLiftedFlow.getNextsLiftedFlow().addAll(dictMethodFlowToAllFirstChildrenFlows.get(oldParentFlow));
                    for (LiftedFlow firstChildrenNextFlow : dictMethodFlowToAllFirstChildrenFlows.get(oldParentFlow)) {
                        firstChildrenNextFlow.getPreviousesLiftedFlow().add(newLiftedFlow);
                    }
                }
            }
        }

        // TODO it seems that I have a bug where the previous flow are not always recorded. I do 
        // an ugly fix here, but I have to correct this...
        for (LiftedFlow newLiftedFlow : newPaths) {
            for (LiftedFlow nextFlow : newLiftedFlow.getNextsLiftedFlow()) {
                nextFlow.getPreviousesLiftedFlow().add(newLiftedFlow);
            }
        }

        this.paths = newPaths;
        this.initialPaths = newInitialPaths;
    }

    // private void getAllPrimitivePaths() {

    //     this.allPrimitivesPath.clear();
    //     // Iterate over all initials flows
    //     for (LiftedFlow initialLiftedFlow : this.initialPaths) {
    //         if (initialLiftedFlow.isMethodLiftedFlow()) {
    //             continue;
    //         }
    //         ArrayList<LiftedFlow> actualPath = new ArrayList<LiftedFlow>();
    //         recursiveFindAllPrimitivePaths(actualPath, initialLiftedFlow);
    //     }
    // }

    // private void recursiveFindAllPrimitivePaths(ArrayList<LiftedFlow> actualPath, LiftedFlow root) {

    //     actualPath.add(root);
    //     if (root.getNextsLiftedFlow().size() == 0) {
    //         this.allPrimitivesPath.add(actualPath);

    //         // Not very clean, but whatever (for now)
    //         this.allPrimitivesPathFlow.addAll(actualPath);
    //     } else {
    //         for (LiftedFlow nextFlow : root.getNextsLiftedFlow()) {
    //             if (!nextFlow.isMethodLiftedFlow()) {
    //                 recursiveFindAllPrimitivePaths((ArrayList<LiftedFlow>) actualPath.clone(), nextFlow);
    //             }
    //         }
    //     }
    // }

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

    SequentialPlan extractPlanAndHierarchyFromSolver(String outputSMTSolver) {
    
        int a = 0;

        String[] outputLines = outputSMTSolver.split("\n");

        List<String> actionsInPlan = Arrays.asList(outputLines);
        List<String> scopeVarActions = Arrays.asList(outputLines);

        // First, extract all the actions which are true
        actionsInPlan = Arrays.asList(actionsInPlan.stream().filter(s -> (s.contains("FLOW_") && s.contains(" true)"))).toArray(String[]::new)); 
        scopeVarActions = Arrays.asList(scopeVarActions.stream().filter(s -> s.contains("SCOPE_")).toArray(String[]::new)); 

        // Get the objects associated with each action
        List<LiftedFlow> actionsObjInPlan = new ArrayList<LiftedFlow>();

        for (String actionInPlan : actionsInPlan) {
            for (LiftedFlow actionObj : this.primitiveTree.nodes) {
                String actionName = actionObj.getUniqueName();

                if (actionInPlan.contains(actionName)) {
                    actionsObjInPlan.add(actionObj);
                }
            }
        }

        SequentialPlan p = new SequentialPlan();
        Hierarchy hierarchy = new Hierarchy();
        
        // Add the roots tasks to the hierarchy
        int numberRootTasks = problem.getInitialTaskNetwork().getTasks().size();
        for (int rootTaskIdx = 0; rootTaskIdx < numberRootTasks; rootTaskIdx++) {
            hierarchy.getRootTasks().add(rootTaskIdx);
            hierarchy.getDecomposition().put(rootTaskIdx, new ArrayList<>());
        }

        System.out.println("==============");
        for (LiftedFlow actionObjInPlan : actionsObjInPlan) {
            System.out.println(actionObjInPlan.getUniqueName());
        }
        System.out.println("==============");
        // take the first action executed
        for (LiftedFlow actionObjInPlan : actionsObjInPlan) {
            
            int sizeRootFromAction = 0;
            // Get the parent of the action
            LiftedFlow node = actionObjInPlan;
            while (node.parentFlow != null) {
                sizeRootFromAction++;
                node = node.parentFlow;
            }

            int parentMethodId = -1;

            for (int i = sizeRootFromAction; i >= 0; i--) {

                // Get the method of this layer
                node = actionObjInPlan;
                for (int j = 0; j < i; j++) {
                    node = node.parentFlow;
                }

                ArrayList<String> argsOperator = new ArrayList<>();


                ArrayList<ScopeVariable> scopesVariable;
                if (i == 0) {
                    scopesVariable = node.getScopeVariablesActionsFlow().get(0);
                } else {
                    scopesVariable = node.getScopeVariables();
                }
                

                // Find all value of the scope of this method/action
                for (ScopeVariable scopeVariable : scopesVariable) {

                    if (scopeVariable.getPossibleValueVariable().size() == 1) {
                        argsOperator.add(scopeVariable.getPossibleValueVariable().iterator().next());
                        continue;
                    }
                    String nameScopeVariable = scopeVariable.getUniqueName();
                    // Get the value from the SMT file
                    for (String scopeVar : scopeVarActions) {
                        String scopeVarExactName = scopeVar.split(" ")[1];
                        if (scopeVarExactName.equals(nameScopeVariable)) {
                            // Extract the value
                            String[] split =  scopeVar.split(" ");
                            String value = split[split.length - 1].substring(0, split[split.length - 1].length() - 1);

                            String objAssociated = null;
                            Integer valueInt = Integer.parseInt(value);
                            for (String objName : this.objNameToUniqueId.keySet()) {
                                if (this.objNameToUniqueId.get(objName) == valueInt) {
                                    objAssociated = objName;
                                    break;
                                }
                            }
                            argsOperator.add(objAssociated);
                            int b = 0;
                        }  
                    }
                }

                if (i > 0) {

                    // Find the ground method associated with this method and argument
                    String nameMethod = node.getMethodName();

                    for (Method groundMethod : problem.getMethods()) {

                        if (!groundMethod.getName().equals(nameMethod)) {
                            continue;
                        }

                        // System.out.println(argMethod);
                        // System.out.println(prettyDisplayMethod(groundMethod, problem));


                        boolean isCorrectMethod = true;
                        for (int argi = 0; argi < groundMethod.getInstantiations().length; argi++) {
                            if (!problem.getConstantSymbols().get(groundMethod.getInstantiations()[argi]).equals(argsOperator.get(argi))) {
                                isCorrectMethod = false;
                                break;
                            }
                        }
                        
                        if (isCorrectMethod) {

                            // Add it into our hierarchy if it not already there
                            // int methodId = this.problem.getMethods().indexOf(groundMethod);
                            int methodId = node.uniqueId;
                            if (!hierarchy.getCounpoudTasks().keySet().contains(methodId)) {
                                hierarchy.getCounpoudTasks().put(methodId, groundMethod);
                                hierarchy.getDecomposition().put(methodId, new ArrayList<>());
                            }

                            // Add this method as the child of the parent method
                            if (parentMethodId != -1 && !hierarchy.getDecomposition().get(parentMethodId).contains(methodId)) {
                                hierarchy.getDecomposition().get(parentMethodId).add(methodId);
                            }

                            parentMethodId = methodId;
                            break;
                        }
                    }
                } else {
                    // TODO change here when they can be multiple actions
                    String nameAction = node.getMacroAction().get(0);

                    boolean actionIsFound = false;
                    for (Action groundAction : problem.getActions()) {

                        if (!groundAction.getName().equals(nameAction)) {
                            continue;
                        }

                        // System.out.println(argMethod);
                        // System.out.println(prettyDisplayMethod(groundMethod, problem));


                        boolean isCorrectAction = true;
                        for (int argi = 0; argi < groundAction.getInstantiations().length; argi++) {
                            if (!problem.getConstantSymbols().get(groundAction.getInstantiations()[argi]).equals(argsOperator.get(argi))) {
                                isCorrectAction = false;
                                break;
                            }
                        }
                        
                        if (isCorrectAction) {

                            // Add it into our hierarchy if it not already there
                            // int actionId = this.problem.getActions().indexOf(groundAction);
                            int actionId = node.uniqueId;
                            hierarchy.getPrimtiveTasks().put(actionId, groundAction);

                            // Add this method as the child of the parent method
                            if (parentMethodId != -1) {
                                hierarchy.getDecomposition().get(parentMethodId).add(actionId);
                            }

                            actionIsFound = true;
                            break;
                        }
                    }
                    if (!actionIsFound) {
                        System.out.println("WHAT !!");
                    }
                }
                a = 0;
            }
        }

        // Create the sequential plan
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
        String command = String.format("./%s --verify %s %s %s", this.path_exec_VAL,  this.domainPath,
                this.problemPath, planFile.getAbsolutePath());

        System.out.println(command);

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
            System.out.println("Cannot verify the plan given. Output returned by executable: \n" + output);
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
     * Return a string containing a method in easily readable format
     * 
     * @param a       The method to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the action in easily readable format
     */
    public String prettyDisplayMethod(Method m, Problem problem) {
        StringBuilder methodToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        methodToDisplay.append("METHOD_" + m.getName());

        // Then, for each argument of this fluent, add the argument into the string
        for (int methodArg : m.getInstantiations()) {
            methodToDisplay.append("_" + problem.getConstantSymbols().get(methodArg));
        }

        return methodToDisplay.toString();
    }

    private void encodeSAT() throws IOException {

        // So what do we have to encode

        StringBuilder allClauses = new StringBuilder();
        allClauses.append("(set-logic QF_ALL)\n");
        allClauses.append("(set-option :produce-models true)\n");

        // Encode all objects
        allClauses.append("; Declare all of our objects and assign value to them\n");
        allClauses.append(encodeDeclarationAllObjectsSAT());

        // Then declare all of the initial predicates
        allClauses.append("; Declare all of our predciates initial values\n");
        allClauses.append(encodeDeclarationAllPredicateSAT());

        // Then declare all of our flow actions
        allClauses.append("; declare all macro actions\n");
        allClauses.append(encodeDeclarationAllMacroActionsSAT());

        // Then declare the all the variables scope (only the scope that can be taken by
        // the flows that will be encoded)
        allClauses.append("; declare all of our macro actions variable scope\n");
        allClauses.append(encodeDeclarationScopeVariablesSAT());

        // Then declare all of the possible flows path
        allClauses.append("; Declare all the macro actions paths\n");
        allClauses.append(declareAllMacroActionsPaths());

        // Then set the value for the initial predicates
        // allClauses.append("Initial values predicates: \n");
        // allClauses.append(encodeSetInitialValueAllPredicateSAT());

        // Add all the constrains on the scopes
        allClauses.append("; Constrains on scopes\n");
        allClauses.append(declaratationAllConstrainsOnScope());

        // Then, for each flows, indicate where it can take its precondition (either a
        // previous flow can satisfied it or it can take it from the initial predicate)
        allClauses.append("; Declaration preconditions of each macro path\n");
        allClauses.append(declarationAllMacroPathPreconditions());

        // Make the at most one flow when there is a parallel flow (not sure it is
        // necessary)

        allClauses.append("(check-sat)\n");
        allClauses.append("(get-model)\n");
        allClauses.append("(exit)\n");
        // Should be about it.

        BufferedWriter writer = new BufferedWriter(new FileWriter(this.filenameSMT));
        writer.write(allClauses.toString());
        writer.flush();
        writer.close();

        int a = 0;
    }

    private String encodeDeclarationAllObjectsSAT() {
        StringBuilder declarationObjects = new StringBuilder();

        for (String typeName : this.dictTypeToObjects.keySet()) {
            Vector<String> allObjsOfType = this.dictTypeToObjects.get(typeName);
            for (int i = 0; i < allObjsOfType.size(); i++) {
                declarationObjects.append("(declare-const " + allObjsOfType.get(i) + " Int)\n");
            }
            // Just use a second loop because it is more estetic on the SMT file generated
            // with this way
            for (int i = 0; i < allObjsOfType.size(); i++) {
                declarationObjects.append("(assert (= " + allObjsOfType.get(i) + " " + this.objNameToUniqueId.get(allObjsOfType.get(i)) + "))\n");
            }
        }
        return declarationObjects.toString();
    }

    // private String encodeDeclarationAllPredicateSAT() {
    // StringBuilder declarationPredicates = new StringBuilder();

    // for (int i = 0; i < this.problem.getFluents().size(); i++) {
    // Fluent f = this.problem.getFluents().get(i);

    // declarationPredicates.append("(declare-const " +
    // prettyDisplayFluent(f, problem) + " Bool)\n");
    // }

    // return declarationPredicates.toString();
    // }

    private String encodeDeclarationAllPredicateSAT() {
        StringBuilder declarationPredicates = new StringBuilder();

        Map<String, Vector<ArrayList<String>>> dictPredicateNameToArgForTrueValue = new HashMap();

        Map<String, Integer> dictPredicateNameToNumArgs = new HashMap<>();

        // Put all the predicate
        for (NamedTypedList pred : problem.getParsedProblem().getPredicates()) {
            String predicateName = pred.getName().getValue();
            int numArgs = pred.getArguments().size();
            dictPredicateNameToArgForTrueValue.put(predicateName, new Vector<ArrayList<String>>());
            dictPredicateNameToNumArgs.put(predicateName, numArgs);
        }

        for (int i = 0; i < this.problem.getFluents().size(); i++) {
            if (this.problem.getInitialState().getPositiveFluents().get(i)) {
                Fluent f = this.problem.getFluents().get(i);
                String predicateName = problem.getPredicateSymbols().get(f.getSymbol());

                // if (!dictPredicateNameToArgForTrueValue.keySet().contains(predicateName)) {
                // dictPredicateNameToArgForTrueValue.put(predicateName, new
                // Vector<ArrayList<String>>());
                // }

                ArrayList<String> args = new ArrayList<String>();
                for (int argi = 0; argi < f.getArguments().length; argi++) {
                    args.add(problem.getConstantSymbols().get(f.getArguments()[argi]));
                }
                dictPredicateNameToArgForTrueValue.get(predicateName).add(args);
            }
        }

        // Now, we can declare all of our predicate
        for (String predicateName : dictPredicateNameToArgForTrueValue.keySet()) {

            Vector<ArrayList<String>> args = dictPredicateNameToArgForTrueValue.get(predicateName);
            int numArgsPredicate = dictPredicateNameToNumArgs.get(predicateName);

            // int numArgsPredicate = 0;
            // if (args.size() > 0) {
            // numArgsPredicate = args.get(0).size();
            // }
            declarationPredicates.append("(define-fun " + predicateName + " ( ");
            for (int i = 0; i < numArgsPredicate; i++) {
                declarationPredicates.append("(x!" + i + " Int) ");
            }
            declarationPredicates.append(") Bool\n");
            declarationPredicates.append("(ite (or\n");
            if (args.size() == 0) {
                declarationPredicates.append("false\n");
            } else {
                for (ArrayList<String> larg : args) {
                    declarationPredicates.append("  (and ");
                    for (int i = 0; i < numArgsPredicate; i++) {
                        declarationPredicates.append("(= x!" + i + " " + larg.get(i) + ") ");
                    }
                    declarationPredicates.append(")\n");
                }
            }

            declarationPredicates.append(") true false\n");
            declarationPredicates.append("))\n");
        }

        return declarationPredicates.toString();
    }


    // private String declaratationAllConstrainsOnScope() {

    //     StringBuilder declarationAllConstrainsOnScope = new StringBuilder();

    //     Stack<Integer> topologicalSortTree = this.primitiveTree.getTopologicalSort();

    //     HashSet<ScopeVariable> scopeAlreadyDeclared = new HashSet<>();

    //     // Consume all the node of the topological sort tree
    //     while (!topologicalSortTree.isEmpty()) {
    //         Integer idxNode = topologicalSortTree.pop();
    //         LiftedFlow node = this.primitiveTree.nodes.get(idxNode);
            
    //         for (ScopeVariable scopeVariable : node.getScopeVariablesActionsFlow().get(0)) {
                
    //             if (scopeVariable.constrains.size() != 0 && !scopeAlreadyDeclared.contains(scopeVariable)) {

    //                 for (ScopeVariable pivot : scopeVariable.constrains.keySet()) {

    //                     declarationAllConstrainsOnScope.append("(assert (=> (= " + scopeVariable.getUniqueName() + " " + pivot.getUniqueName() + ") (and \n");

    //                     // Should know all the LiftedFlow which have implies each one of these condtion
    //                     for (Triple<LiftedFlow, ScopeVariable, ScopeVariable> shouldBeEqualTo : scopeVariable.constrains.get(pivot)) {
    //                         declarationAllConstrainsOnScope.append("(=> " + shouldBeEqualTo.getLeft().getUniqueName() + " (= " + shouldBeEqualTo.getMiddle().getUniqueName() + " " + shouldBeEqualTo.getRight().getUniqueName() + ") )\n");    
    //                     }
    //                     declarationAllConstrainsOnScope.append(")))\n");    
    //                 }
    //                 scopeAlreadyDeclared.add(scopeVariable);
    //             }
    //         }
    //     }
    //     return declarationAllConstrainsOnScope.toString();
    // }


    private String declaratationAllConstrainsOnScope() {

        StringBuilder declarationAllConstrainsOnScope = new StringBuilder();

        Stack<Integer> topologicalSortTree = this.primitiveTree.getTopologicalSort();

        HashSet<ScopeVariable> scopeAlreadyDeclared = new HashSet<>();

        // Consume all the node of the topological sort tree
        while (!topologicalSortTree.isEmpty()) {
            Integer idxNode = topologicalSortTree.pop();
            LiftedFlow node = this.primitiveTree.nodes.get(idxNode);
            
            for (ScopeVariable scopeVariable : node.getScopeVariablesActionsFlow().get(0)) {

                ArrayList<ConstrainsOnScopeVariable> constrainsScopeVar = scopeVariable.getConstrains();
                
                if (constrainsScopeVar.size() > 0 && !scopeAlreadyDeclared.contains(scopeVariable)) {

                    for (ConstrainsOnScopeVariable constrainOnScopeVar : constrainsScopeVar) {
                        declarationAllConstrainsOnScope.append("(assert (=> (and (= " + scopeVariable.getUniqueName() + " " + constrainOnScopeVar.pivot.getUniqueName() + ")");
                        for (ScopeVariable pivotShouldBeDifferentTo : constrainOnScopeVar.constrainsOnPivot) {
                            declarationAllConstrainsOnScope.append("(not (= " + constrainOnScopeVar.pivot.getUniqueName() + " " + pivotShouldBeDifferentTo.getUniqueName() + ")) ");
                        }
                        declarationAllConstrainsOnScope.append(") (and \n");
                        for (int i = 0; i < constrainOnScopeVar.liftedFlows.size(); i++) {
                            declarationAllConstrainsOnScope.append("(=> " + constrainOnScopeVar.liftedFlows.get(i).getUniqueName());
                            for (Pair<ScopeVariable, ScopeVariable> pairThatMustBeEquals : constrainOnScopeVar.pairsScopeThatMustBeEquals.get(i)) {
                                declarationAllConstrainsOnScope.append(" (= " + pairThatMustBeEquals.getLeft().getUniqueName() + " " + pairThatMustBeEquals.getRight().getUniqueName() + ") )\n");    
                            }
                        }
                        declarationAllConstrainsOnScope.append(")))\n"); 
                    }
                    scopeAlreadyDeclared.add(scopeVariable);
                }
            }
        }
        return declarationAllConstrainsOnScope.toString();
    }

    private String encodeDeclarationAllMacroActionsSAT() {
        StringBuilder declarationMacroActions = new StringBuilder();

        Stack<Integer> topologicalSortTree = this.primitiveTree.getTopologicalSort();

        // Consume all the node of the topological sort tree
        while (!topologicalSortTree.isEmpty()) {
            Integer idxNode = topologicalSortTree.pop();
            LiftedFlow node = this.primitiveTree.nodes.get(idxNode);

            declarationMacroActions.append("; " + node + "\n");

            declarationMacroActions.append("(declare-const " +
                    node.getUniqueName() + " Bool)\n");

        }

        return declarationMacroActions.toString();
    }

    // private String encodeSetInitialValueAllPredicateSAT() {

    // StringBuilder initialValueAllPredicates = new StringBuilder();

    // for (int i = 0; i < this.problem.getFluents().size(); i++) {
    // Fluent f = this.problem.getFluents().get(i);

    // if (this.problem.getInitialState().getPositiveFluents().get(i)) {

    // initialValueAllPredicates
    // .append("(assert (= " +
    // prettyDisplayFluent(f, problem)
    // + " true))\n");
    // } else {

    // initialValueAllPredicates
    // .append("(assert (= "
    // + prettyDisplayFluent(f, problem)
    // + " false))\n");
    // }
    // }
    // return initialValueAllPredicates.toString();
    // }

    private String declareAllMacroActionsPaths() {

        StringBuilder allMacroActionsPath = new StringBuilder();

        // I've come up with an algo for that, but I do not know if it is the most optimal
        // Iterate over our primitive tree in a topological way
        Stack<Integer> topologicalSortTree = this.primitiveTree.getTopologicalSort();

        // Map<Integer, String> flowToFormula = new HashMap<Integer, String>();
        String[] flowToFormula = new String[this.primitiveTree.nodes.size()]; 
        HashSet<String> fullFormula = new HashSet<String>();
        ArrayList<ArrayList<LiftedFlow>> allConcurrentsActions = new ArrayList<>(); 
        int[] dictNodeToIdxConcurrentActions = new int[this.primitiveTree.nodes.size()];
        for (int i = 0; i < this.primitiveTree.nodes.size(); i++) {
            dictNodeToIdxConcurrentActions[i] =  -1;
        }

        // Consume all the node of the topological sort tree
        while (!topologicalSortTree.isEmpty()) {
            Integer idxNode = topologicalSortTree.pop();
            LiftedFlow node = this.primitiveTree.nodes.get(idxNode);
            HashSet<Integer> parentsNodeIdx = this.primitiveTree.parentsNodesIdx.get(idxNode);
            // if (parentsNodeIdx.size() == 0) {
            //     flowToFormula[idxNode] = node.getUniqueName();
            // }
            // else if (parentsNodeIdx.size() == 1) {
            //     flowToFormula[idxNode] = "(and " + node.getUniqueName() + " " + flowToFormula[parentsNodeIdx.iterator().next()] + ")";
            // }
            // else {
            //     StringBuilder formulaNode = new StringBuilder();
            //     formulaNode.append("(and " + node.getUniqueName() + " (or ");
            //     for (Integer idxParentNode : parentsNodeIdx) {
            //         formulaNode.append(flowToFormula[idxParentNode] + " ");
            //     }
            //     formulaNode.append("))");
            //     flowToFormula[idxNode] = formulaNode.toString();
            // }


            // if (this.primitiveTree.childrenNodesIdx.get(idxNode).size() == 0) {
            //     fullFormula.add(flowToFormula[idxNode]);
            // }

            // Add all concurrent actions in the at most list
            if (this.primitiveTree.childrenNodesIdx.get(idxNode).size() > 1) {
                // Check if those children are already in a HashSet
                int idxMutexAction = -1;
                for (Integer idxChild : this.primitiveTree.childrenNodesIdx.get(idxNode)) {
                    if (dictNodeToIdxConcurrentActions[idxChild] != -1) {
                        idxMutexAction = dictNodeToIdxConcurrentActions[idxChild];
                        break;
                    }
                }
                if (idxMutexAction == -1) {
                    allConcurrentsActions.add(new ArrayList<>());
                    idxMutexAction = allConcurrentsActions.size() - 1;
                }
                for (Integer idxChild : this.primitiveTree.childrenNodesIdx.get(idxNode)) {
                    if (!allConcurrentsActions.get(idxMutexAction).contains(this.primitiveTree.nodes.get(idxChild))) {
                        allConcurrentsActions.get(idxMutexAction).add(this.primitiveTree.nodes.get(idxChild));
                        dictNodeToIdxConcurrentActions[idxChild] = idxMutexAction;
                    }
                }
            }
            if (this.primitiveTree.parentsNodesIdx.get(idxNode).size() > 1) {
                // Check if those children are already in a HashSet
                int idxMutexAction = -1;
                for (Integer idxParent : this.primitiveTree.parentsNodesIdx.get(idxNode)) {
                    if (dictNodeToIdxConcurrentActions[idxParent] != -1) {
                        idxMutexAction = dictNodeToIdxConcurrentActions[idxParent];
                        break;
                    }
                }
                if (idxMutexAction == -1) {
                    allConcurrentsActions.add(new ArrayList<>());
                    idxMutexAction = allConcurrentsActions.size() - 1;
                }
                for (Integer idxParent : this.primitiveTree.parentsNodesIdx.get(idxNode)) {
                    if (!allConcurrentsActions.get(idxMutexAction).contains(this.primitiveTree.nodes.get(idxParent))) {
                        allConcurrentsActions.get(idxMutexAction).add(this.primitiveTree.nodes.get(idxParent));
                        dictNodeToIdxConcurrentActions[idxParent] = idxMutexAction;
                    }

                }
            }
        }

        // allMacroActionsPath.append("(assert (or\n");
        // for (String path : fullFormula) {
        //     allMacroActionsPath.append(path + " \n");
        // }
        // allMacroActionsPath.append("))\n");

        // One of the root action should be true
        allMacroActionsPath.append("; one of the root action should be true\n");
        allMacroActionsPath.append("(assert (or ");
        for (Integer rootNode : this.primitiveTree.rootNodesIdx) {
            allMacroActionsPath.append(this.primitiveTree.nodes.get(rootNode).getUniqueName() + " ");
        }
        allMacroActionsPath.append("))\n");


        allMacroActionsPath.append("; action true => one of its child action is true\n");
        Stack<Integer> topologicalSortTree2 = this.primitiveTree.getTopologicalSort();
        // Consume all the node of the topological sort tree
        while (!topologicalSortTree2.isEmpty()) {
            Integer idxNode = topologicalSortTree2.pop();
            LiftedFlow node = this.primitiveTree.nodes.get(idxNode);
            HashSet<Integer> childrenNode = this.primitiveTree.childrenNodesIdx.get(idxNode);

            if (childrenNode.size() == 0) {
                continue;
            }

            else if (childrenNode.size() == 1) {
                LiftedFlow childNode = this.primitiveTree.nodes.get(childrenNode.iterator().next());
                allMacroActionsPath.append("(assert (=> " + node.getUniqueName() + " " + childNode.getUniqueName() + "))\n");
            }
            
            else {
                allMacroActionsPath.append("(assert (=> " + node.getUniqueName() + " (or ");
                for (Integer idxChild : this.primitiveTree.childrenNodesIdx.get(idxNode)) {
                    allMacroActionsPath.append(this.primitiveTree.nodes.get(idxChild).getUniqueName() + " ");
                }
                allMacroActionsPath.append(")))\n");
            }
        }


        // Add as well the at most one action for all concurrents actions
        allMacroActionsPath.append("; at most one action\n");
        Stack<Integer> topologicalSortTree3 = this.primitiveTree.getTopologicalSort();
        HashSet<String> pairAlreadySeen = new HashSet<String>();
        // Consume all the node of the topological sort tree
        while (!topologicalSortTree3.isEmpty()) {
            Integer idxNode = topologicalSortTree3.pop();

            if (this.primitiveTree.parentsNodesIdx.get(idxNode).size() > 1) {

                List<Integer> concurrentIdxActionList = new ArrayList<>(this.primitiveTree.parentsNodesIdx.get(idxNode));
                // All thoses actions should be mutex
                for (int i = 0; i < concurrentIdxActionList.size(); i++) {
                    for (int j = i+1; j < concurrentIdxActionList.size(); j++) {
                        int idxParentNode1 = concurrentIdxActionList.get(i);
                        int idxParentNode2 = concurrentIdxActionList.get(j);
                        int min = Math.min(idxParentNode1, idxParentNode2);
                        int max = Math.max(idxParentNode1, idxParentNode2);
                        String key = min + "_" + max;
                        if (!pairAlreadySeen.contains(key)) {
                            allMacroActionsPath.append("(assert (or (not " + this.primitiveTree.nodes.get(min).getUniqueName() + ") (not " + this.primitiveTree.nodes.get(max).getUniqueName() + ")))\n");
                            pairAlreadySeen.add(key);
                        }
                    }
                }


            }

            if (this.primitiveTree.childrenNodesIdx.get(idxNode).size() > 1) {

                List<Integer> concurrentIdxActionList = new ArrayList<>(this.primitiveTree.childrenNodesIdx.get(idxNode));
                // All thoses actions should be mutex
                for (int i = 0; i < concurrentIdxActionList.size(); i++) {
                    for (int j = i+1; j < concurrentIdxActionList.size(); j++) {
                        int idxChildNode1 = concurrentIdxActionList.get(i);
                        int idxChildNode2 = concurrentIdxActionList.get(j);
                        int min = Math.min(idxChildNode1, idxChildNode2);
                        int max = Math.max(idxChildNode1, idxChildNode2);
                        String key = min + "_" + max;
                        if (!pairAlreadySeen.contains(key)) {
                            allMacroActionsPath.append("(assert (or (not " + this.primitiveTree.nodes.get(min).getUniqueName() + ") (not " + this.primitiveTree.nodes.get(max).getUniqueName() + ")))\n");
                            pairAlreadySeen.add(key);
                        }
                    }
                }


            }

        }
        // for (ArrayList<LiftedFlow> concurrentIdxAction : allConcurrentsActions) {
        //     for (int i = 0; i < concurrentIdxAction.size(); i++) {
        //         for (int j = i+1; j < concurrentIdxAction.size(); j++) {
        //             String l1 = concurrentIdxAction.get(i).getUniqueName();
        //             String l2 = concurrentIdxAction.get(j).getUniqueName();
        //             allMacroActionsPath.append("(assert (or (not " + l1 + ") (not " + l2 + ")))\n");
        //         }
        //     }
        // }

        // Now, the question is how to write all those paths from the primitive tree

        // For now, just write all the path possible (TODO improve this later)
        // allMacroActionsPath.append("(assert (or\n");
        // for (List<LiftedFlow> primitivePath : this.allPrimitivesPath) {
        //     allMacroActionsPath.append("(and ");
        //     for (LiftedFlow primitiveFlow : primitivePath) {
        //         allMacroActionsPath.append(primitiveFlow.getUniqueName() + " ");
        //     }
        //     allMacroActionsPath.append(")\n");
        // }
        // allMacroActionsPath.append("))\n");
        return allMacroActionsPath.toString();
    }

    private String encodeDeclarationScopeVariablesSAT() {
        StringBuilder declarationScopeVariables = new StringBuilder();

        HashSet<ScopeVariable> scopeAlreadyDeclared = new HashSet<ScopeVariable>();

        for (LiftedFlow flow : this.primitiveTree.nodes) {
            for (ArrayList<ScopeVariable> arrayScope : flow.getScopeVariablesActionsFlow()) {
                for (ScopeVariable scopeVariable : arrayScope) {
                    if (!scopeAlreadyDeclared.contains(scopeVariable) && !scopeVariable.isConstant()) {
                        declarationScopeVariables.append("(declare-const " + scopeVariable.getUniqueName() + " Int)\n");
                        // Indicate as well all the different value that this scope variable can take

                        declarationScopeVariables.append("(assert (or ");
                        for (String value : scopeVariable.getPossibleValueVariable()) {
                            declarationScopeVariables
                                    .append("(= " + scopeVariable.getUniqueName() + " " + value + ") ");
                        }
                        declarationScopeVariables.append("))\n");
                        scopeAlreadyDeclared.add(scopeVariable);
                    }
                }
            }
        }

        return declarationScopeVariables.toString();
    }


    private String declarationAllMacroPathPreconditions() {

            StringBuilder declarationAllMacroPathPrecondition = new StringBuilder();
    
            // Iterate over our primitive tree in a topological way
            Stack<Integer> topologicalSortTree = this.primitiveTree.getTopologicalSort();
    
            // Consume all the node of the topological sort tree
            while (!topologicalSortTree.isEmpty()) {
                Integer idxNode = topologicalSortTree.pop();
                LiftedFlow node = this.primitiveTree.nodes.get(idxNode);

                if (this.layer == 4 && node.getUniqueName().equals("FLOW_drive_172")) {
                    int a = 0;
                }
    
                // Iterate over all preconditions of the node
                for (CertifiedPredicate precondition : node.preconditionPredicates) {
    
                    declarationAllMacroPathPrecondition.append("; " + precondition + "\n");
    
                    declarationAllMacroPathPrecondition.append("(assert (=> " + node.getUniqueName() + " ");
    
                    // Get the solver associated with this precondition
                    SolverPrecondition solverPred = node.preconditionSolver.get(precondition);

                    if (solverPred.isInvariantTrue) {
                        // We have nothing to do here
                        declarationAllMacroPathPrecondition.append("true))\n");
                        continue;
                    }
                    else if (solverPred.isStaticPrecondition) {
                        // We just have to check the condition at the beginning
                        if (!precondition.isPositive) {
                            declarationAllMacroPathPrecondition.append("(not ");
                        }

                        declarationAllMacroPathPrecondition.append(" (" + precondition.predicateName + " ");
                        for (ScopeVariable var : precondition.scope) {
                            declarationAllMacroPathPrecondition.append(var.getUniqueName() + " ");
                        }
                        declarationAllMacroPathPrecondition.append(")"); // Finish function
                        if (!precondition.isPositive) {
                            declarationAllMacroPathPrecondition.append(")"); // Finish not
                        }
                        declarationAllMacroPathPrecondition.append("))\n"); // Finish assert and =>

                        continue;
                    }

                    if ((solverPred.constrainsOnScope.size() > 0 || solverPred.scopeVarThatMustBeEquals.size() > 0) && solverPred.mustCheckInitValue) {
                        declarationAllMacroPathPrecondition.append("(or ");
                    }


                    if (solverPred.constrainsOnScope.size() > 0) {
                        // TODO should check the certifier !!!!

                        
                        // Add the constrains 
                        for (ScopeVariable constrains : solverPred.constrainsOnScope) {
                            if (constrains.getConstrains().size() > 0) {
                                declarationAllMacroPathPrecondition.append("(or ");
                            }

                            for (ConstrainsOnScopeVariable constrainsOnScopeVariable : constrains.getConstrains()) {
                                declarationAllMacroPathPrecondition.append("(= " + constrains.getUniqueName() + " " + constrainsOnScopeVariable.pivot.getUniqueName() + ") ");
                            }
                            
                            if (constrains.getConstrains().size() > 0) {
                                declarationAllMacroPathPrecondition.append(")"); // Finish or
                            }
                        }

                        if (solverPred.constrainsOnScope.size() > 1) {
                            declarationAllMacroPathPrecondition.append(")");
                        }
                    }

                    if (solverPred.scopeVarThatMustBeEquals.size() > 0) {
                        if (solverPred.scopeVarThatMustBeEquals.size() > 1) {
                            declarationAllMacroPathPrecondition.append("(and ");
                        }
                        for (Pair<ScopeVariable, ScopeVariable> scopesThatMustBeEqual : solverPred.scopeVarThatMustBeEquals) {
                            declarationAllMacroPathPrecondition.append("(= " + scopesThatMustBeEqual.getLeft().getUniqueName() + " " + scopesThatMustBeEqual.getRight().getUniqueName() + ") ");
                        }
                        if (solverPred.scopeVarThatMustBeEquals.size() > 1) {
                            declarationAllMacroPathPrecondition.append(")"); // End or
                        }
                    }


                    if (solverPred.mustCheckInitValue) {

                        if (!precondition.isPositive) {
                            declarationAllMacroPathPrecondition.append("(not ");
                        }

                        declarationAllMacroPathPrecondition.append(" (" + precondition.predicateName + " ");
                        for (ScopeVariable var : precondition.scope) {
                            declarationAllMacroPathPrecondition.append(var.getUniqueName() + " ");
                        }
                        declarationAllMacroPathPrecondition.append(")"); // Finish function
                        if (!precondition.isPositive) {
                            declarationAllMacroPathPrecondition.append(")"); // Finish not
                        }
                    }

                    if (solverPred.constrainsOnScope.size() > 0 && solverPred.mustCheckInitValue) {
                        declarationAllMacroPathPrecondition.append(")"); // Finish the or
                    }

                    declarationAllMacroPathPrecondition.append("))\n"); // Finish assert and =>
                }
            }
    
            return declarationAllMacroPathPrecondition.toString();
        }

    // private void createPrimitiveTree() {

    //     this.primitiveTree.clear();

    //     for (List<LiftedFlow> primitivePath : this.allPrimitivesPath) {
    //         for (int i = 0; i < primitivePath.size(); i++) {
    //             LiftedFlow f = primitivePath.get(i);

    //             if (i == 0) {
    //                 this.primitiveTree.addNodeAndParentIfNotExist(f, null);
    //             } else {
    //                 LiftedFlow parent = primitivePath.get(i - 1);
    //                 this.primitiveTree.addNodeAndParentIfNotExist(f, parent);
    //             }
    //         }
    //     }
    //     int a = 0;
    // }

    private void createPrimitiveTreeQuick() {

        // For now clean everything at the beginning
        // There is surey a smarter way to do this
        this.primitiveTree.clear();
        for (LiftedFlow f : this.paths) {
            f.isPrimitiveFlow = false;
            f.numberChildrenPrimitiveFlow = 0;
        }

        Stack<LiftedFlow> poolNodesToIterate = new Stack<LiftedFlow>();
        for (LiftedFlow initPaths : this.initialPaths) {
            if (!initPaths.isMethodLiftedFlow()) {
                initPaths.isPrimitiveFlow = true;
                poolNodesToIterate.add(initPaths);
            }   
        }

        HashSet<LiftedFlow> nodesAlreadySeen = new HashSet<LiftedFlow>();
        HashSet<LiftedFlow> actionNodeNotPrimitive = new HashSet<LiftedFlow>();

        // Now, try to create the tree. if we arrive to a method node. Remove all the tree until the last embrachement
        while (poolNodesToIterate.size() > 0) {

            LiftedFlow node = poolNodesToIterate.pop();
            boolean atLeastOneActionChildNode = false;

            if (node.nextsFlow.size() == 0) {
                // Tail node. We have arrived to the end here !
                continue;
            }

            for (LiftedFlow childNode : node.nextsFlow) {
                if (childNode.isMethodLiftedFlow() || actionNodeNotPrimitive.contains(childNode)) {
                    continue;
                }

                atLeastOneActionChildNode = true;
                // Increase our number of children primitive flow
                node.numberChildrenPrimitiveFlow++;

                if (!nodesAlreadySeen.contains(childNode)) {
                    // Set it as primitive flow 
                    childNode.isPrimitiveFlow = true;
                    // Add this node to the pool of nodes to iterate
                    poolNodesToIterate.add(childNode);

                    nodesAlreadySeen.add(childNode);
                }
            }

            // We have to prune the tree until the last embranchement
            if (!atLeastOneActionChildNode) {
                Stack<LiftedFlow> poolNodesToPrune = new Stack<>();
                poolNodesToPrune.add(node);
                while (poolNodesToPrune.size() > 0) {
                    LiftedFlow nodeToPrune = poolNodesToPrune.pop();
                    actionNodeNotPrimitive.add(nodeToPrune);
                    nodeToPrune.numberChildrenPrimitiveFlow--;
                    if (nodeToPrune.numberChildrenPrimitiveFlow == 0) {
                        nodeToPrune.isPrimitiveFlow = false;
                        // Add all its parents primitive flow to the pool
                        for (LiftedFlow previous : nodeToPrune.getPreviousesLiftedFlow()) {
                            if (previous.isPrimitiveFlow) {
                                poolNodesToPrune.add(previous);
                            }
                        }
                    }
                }
            }
        }

        // Create our tree now 
        this.primitiveTree.clear();

        for (LiftedFlow node : this.paths) {
            if (node.isPrimitiveFlow) {

                // this.primitiveTree.addNodeIfNotExist(node);
                boolean isRootNode = true;
                for (LiftedFlow parentNode : node.getPreviousesLiftedFlow()) {
                    if (parentNode.isPrimitiveFlow) {
                        isRootNode = false;
                        // this.primitiveTree.addParentToNode(node, parentsNode);
                        this.primitiveTree.addNodeAndParentIfNotExist(node, parentNode);
                    }
                }
                if (isRootNode) {
                    this.primitiveTree.addRootNode(node);
                }
            }
        }

        int a = 0;
    }

    private LIFTED_FAM_GROUP_UNIFIER predicatesAreInSameLiftedFamGroup(CertifiedPredicate pred1,
            CertifiedPredicate pred2, ArrayList<String> constrainsToSuccessfullyUnify) {

        // Check if this predicate is into a liftedFam
        for (Candidate liftedFamGroup : this.liftedFamGroups) {
            for (AtomCandidate atomCandidate : liftedFamGroup.mutexGroup) {
                if (atomCandidate.predSymbolName.equals(pred1.predicateName)) {

                    boolean canBeRepresentedByLiftedFamGroup = true;
                    // Check if the type of each arg is also identical
                    for (int argi = 0; argi < pred1.scope.size(); argi++) {
                        if (!atomCandidate.candidateParent.variables.get(atomCandidate.paramsId.get(argi)).typeName
                                .equals(pred1.scope.get(argi).getType())) {
                            canBeRepresentedByLiftedFamGroup = false;
                            break;
                        }
                    }
                    if (!canBeRepresentedByLiftedFamGroup) {
                        continue;
                    }

                    // We can try to unify those two predicates here
                    // We have two cases here, either we can unify
                    // or we can only unify only if some constrains are filled
                    // The fourth argument indicate the values of each
                    // argument of the certified predicate to be able to unified the two predicates
                    return canUnifyPreds(pred2, pred1, atomCandidate, constrainsToSuccessfullyUnify);
                    // return true;
                    // } else {
                    // int b = 0;
                    // }
                    // int a = 0;

                }
            }
        }

        return LIFTED_FAM_GROUP_UNIFIER.FAILED;
        // return false;
    }

    public LIFTED_FAM_GROUP_UNIFIER canUnifyPreds(CertifiedPredicate pred1, CertifiedPredicate pred2,
            AtomCandidate atomThatCanBeBound, ArrayList<String> constrainsToSuccessfullyUnify) {

        HashSet<AtomVariable> varsBoundByPredicateToCheck = new HashSet<AtomVariable>();

        // First bound the first predicate
        for (int argi = 0; argi < pred1.scope.size(); argi++) {
            AtomVariable var = atomThatCanBeBound.candidateParent.variables.get(atomThatCanBeBound.paramsId.get(argi));

            // If the variable is a countedthis.objNameToUniqueId variable, it can take any value, there is no
            // need to bound
            if (var.isCountedVar) {
                continue;
            }

            else if (pred1.scope.get(argi).getPossibleValueVariable().size() > 1) {

                // Here we can bound the variable with the name of the scope value.
                var.value = pred1.scope.get(argi).getUniqueName();
                varsBoundByPredicateToCheck.add(var);
            } else {
                // Bound the variable
                var.value = pred1.scope.get(argi).getPossibleValueVariable().iterator().next();
                varsBoundByPredicateToCheck.add(var);
            }
        }

        for (AtomCandidate atomCandidate : atomThatCanBeBound.candidateParent.mutexGroup) {
            if (atomCandidate.predSymbolName.equals(pred2.predicateName)) {

                boolean canBeRepresentedByLiftedFamGroup = true;
                // Check if the type of each arg is also identical
                for (int argi = 0; argi < pred2.scope.size(); argi++) {
                    AtomVariable var = atomCandidate.candidateParent.variables.get(atomCandidate.paramsId.get(argi));
                    if (!var.typeName.equals(pred2.scope.get(argi).getType())) {

                        return LIFTED_FAM_GROUP_UNIFIER.FAILED;
                    }
                    // Bound the variable
                    if (var.isCountedVar) {
                        continue;
                    } else if (pred2.scope.get(argi).getPossibleValueVariable().size() > 1) {
                        String valueOutputCertifiedPredArgi = pred2.scope.get(argi).getUniqueName();
                        // Check if the variable is correctly bound by the predicate to check
                        if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                            // It's correct here, we can continue
                            continue;
                        } else {
                            // The var is bound to another value... We need to indicate the constrains here
                            constrainsToSuccessfullyUnify.set(argi, var.value);
                            canBeRepresentedByLiftedFamGroup = false;
                            // break;
                        }
                    } else {
                        String valueOutputCertifiedPredArgi = pred2.scope.get(argi).getPossibleValueVariable()
                                .iterator().next();
                        // Check if the variable is correctly bound by the predicate to check
                        if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                            // It's correct here, we can continue
                            continue;
                        } else {
                            // The var is bound to another value... No correct here
                            constrainsToSuccessfullyUnify.set(argi, var.value);
                            canBeRepresentedByLiftedFamGroup = false;
                            // break;
                        }
                    }

                }
                // Else, it means that we already have a predicate of the lifted fam ground in
                // output
                // Clean the variable
                for (AtomVariable varBound : varsBoundByPredicateToCheck) {
                    varBound.value = null;
                }

                if (canBeRepresentedByLiftedFamGroup) {
                    return LIFTED_FAM_GROUP_UNIFIER.SUCCESS;
                } else {
                    return LIFTED_FAM_GROUP_UNIFIER.SUCCESS_WITH_CONSTRAINS;
                }
            }
        }

        // Clean the variables
        for (AtomVariable varBound : varsBoundByPredicateToCheck) {
            varBound.value = null;
        }
        return LIFTED_FAM_GROUP_UNIFIER.FAILED;
    }

    /**
     * Indicate for each LiftedFlow of the primitive tree, the set of the
     * predicates that it know the value as well as the set of the predicates
     * that are true depending of the parent used (for the input (before the action
     * is called), and for the output (afer the action is called))
     */
    private void computeCertifiedPredicatesPrimitiveTree() {

        System.out.println("Compute input and output certified predicates...\n");


        // Not sure we have to do this
        for (LiftedFlow f : this.primitiveTree.nodes) {
            f.cleanAllConstrainsScope();
        }

        // Get the topological sort of the primitive tree to iterate over it
        Stack<Integer> topologicalSortTree = this.primitiveTree.getTopologicalSort();

        // Consume all the node of the topological sort tree
        while (!topologicalSortTree.isEmpty()) {
            Integer idxNode = topologicalSortTree.pop();
            LiftedFlow node = this.primitiveTree.nodes.get(idxNode);
            // TODO instead of clearing them and and redo all the work,
            // Maybe we could only update them with the new paths...
            // At worst, we can still only clear and redo the work
            // of all the children of the new primitive actions and the new primitive
            // actions
            node.inputCertifiedPredicates.clear();
            node.outputCertifiedPredicates.clear();
            // Clean all the constrains as well (not sure we must do this ?)



            System.out.println("==========");
            System.out.println("For node: " + node);

            // if (node.getUniqueName().equals("FLOW_drive_229") || node.getUniqueName().equals("FLOW_drive_175")) {
            //     int a = 0;
            // }

            // if (node.getUniqueName().equals("FLOW_drive_146") || node.getUniqueName().equals("FLOW_drive_98")) {
            //     int a = 0;
            // }

            // if (layer == 2 && (node.getUniqueName().equals("FLOW_noop_68") || node.getUniqueName().equals("FLOW_noop_29"))) {
            //     int a = 0;
            // }

            // TODO There is no need to clear this one
            node.preconditionPredicates.clear();

            // Get the parents of the certified predicate
            HashSet<LiftedFlow> parentsNode = this.primitiveTree.getParents(idxNode);

            // Compute the input certified predicates (predicate which we are sure are
            // true before the action is called)
            node.computeInputCertifiedPredicatesFromParents(parentsNode);

            // Compute the predicate which are genrated with the precondition
            // TODO There is no need to regenerate them
            node.computePredicatesFromPreconditions();

            // node.findAllConstrainsOnScopeVar(this.staticPredicates, this.liftedFamGroups);


            node.determinateHowToResolvePreconditions(this.staticPredicates, this.liftedFamGroups);

            // Compute the output certified predicates of the action (predicate
            // which we are sure are true after the action is called)
            node.computeOutputCertifiedPredicates(this.staticPredicates, this.liftedFamGroups);

            // for (CertifiedPredicate precondition : node.preconditionSolver.keySet()) {
            //     System.out.println("To solve: ");
            //     System.out.println(precondition);
            //     System.out.println(node.preconditionSolver.get(precondition));
            // }

            if (this.layer == 4) {
                int a = 0;
                // System.out.println(declaratationAllConstrainsOnScope());
            }

            int a = 0;
        }

        // Some test
        // Stack<Integer> topologicalSortTree2 = this.primitiveTree.getTopologicalSort();
        // while (!topologicalSortTree2.isEmpty()) {
        //     Integer idxNode = topologicalSortTree2.pop();
        //     LiftedFlow node = this.primitiveTree.nodes.get(idxNode);
        //     for (ScopeVariable sv : node.getScopeVariablesActionsFlow().get(0)) {
        //         if (sv.constrains.size() != 0) {
        //             for (ScopeVariable con : sv.constrains.keySet()) {
        //                 System.out.println(sv.getUniqueName() + " == " + con.getUniqueName() + " => ");
        //                 for (Pair<ScopeVariable, ScopeVariable> pair : sv.constrains.get(con)) {
        //                     System.out.println(pair.getLeft().getUniqueName() + " = " + pair.getRight().getUniqueName() + " | ");
        //                 }
                        
        //             }
        //         }
        //     }
        //     int a = 0;
        // }
        int b= 0;
    }

    private void preprocessing() {
        // Find each object and give a value for each object of each type
        this.dictTypeToObjects = new HashMap<String, Vector<String>>();
        for (String typeName : this.problem.getTypes()) {
            this.dictTypeToObjects.put(typeName, new Vector<String>());
        }
        // Now iterate over each object to get the type
        for (TypedSymbol<String> obj : this.problem.getParsedProblem().getConstants()) {
            String nameObj = obj.getValue();
            String typeObj = obj.getTypes().get(0).getValue();
            System.out.println(nameObj + " " + typeObj);
            this.dictTypeToObjects.get(typeObj).add(nameObj);
        }

        this.objNameToUniqueId = objNameToUniqueId();

        // For each method, map its name to the object parsed method associated
        // + For each method, compute the number of children that this method can take
        this.methodNameToObj = new HashMap<String, ParsedMethod>();
        this.liftedMethodToNumberSubtasks = new HashMap<String, Integer>();
        for (ParsedMethod methodObj : this.problem.getParsedProblem().getMethods()) {
            String nameMethod = methodObj.getName().getValue();
            this.methodNameToObj.put(nameMethod, methodObj);

            // Ugly way to get the number of subtasks of a lifted method, but it is done
            // only once, so who care
            for (Method m : problem.getMethods()) {
                if (m.getName().equals(nameMethod)) {
                    this.liftedMethodToNumberSubtasks.put(nameMethod, m.getSubTasks().size());
                    break;
                }
            }
        }

        this.actionNameToObj = new HashMap<String, ParsedAction>();
        for (ParsedAction actionObj : this.problem.getParsedProblem().getActions()) {
            String nameAction = actionObj.getName().getValue();
            this.actionNameToObj.put(nameAction, actionObj);
        }

        // Get all the static predicates
        this.staticPredicates = preprocessingComputeStaticPredicates(problem);

        // Create a map from the name of an object to its type
        this.dictObjNameToType = preprocessingComputeDictObjectNameToType(problem);
    }

    private HashSet<String> preprocessingComputeStaticPredicates(Problem problem) {

        HashSet<String> staticPredicates = new HashSet<String>();
        // Iterate over all predicates name
        for (String predicateName : problem.getPredicateSymbols()) {
            if (predicatIsStatic(predicateName, problem)) {
                staticPredicates.add(predicateName);
            }
        }
        return staticPredicates;
    }

    public Map<String, String> preprocessingComputeDictObjectNameToType(Problem problem) {

        Map<String, String> dictObjNameToType = new HashMap<>();
        for (TypedSymbol<String> obj : problem.getParsedProblem().getConstants()) {
            dictObjNameToType.put(obj.getValue(), obj.getTypes().get(0).getValue());
        }
        return dictObjNameToType;
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

    private Map<String, Integer> objNameToUniqueId() {

        Map<String, Integer> mapObjNameToUniqueId = new HashMap<String, Integer>();

        int valueObj = 0;
        for (String typeName : this.dictTypeToObjects.keySet()) {
            Vector<String> allObjsOfType = this.dictTypeToObjects.get(typeName);
            for (int i = 0; i < allObjsOfType.size(); i++) {
                mapObjNameToUniqueId.put(allObjsOfType.get(i), valueObj);
                valueObj++;
            }
        }
        return mapObjNameToUniqueId;
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
        fluentToDisplay.append("FLUENT_" + problem.getPredicateSymbols().get(f.getSymbol()));

        // Then, for each argument of this fluent, add the argument into the string
        for (int fluentArg : f.getArguments()) {
            fluentToDisplay.append("_" + problem.getConstantSymbols().get(fluentArg));
        }

        return fluentToDisplay.toString();
    }

}
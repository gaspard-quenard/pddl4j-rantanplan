package pddlparser.csp_numeric_variables_sasPlus_recursiveSupport;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.concurrent.ThreadLocalRandom;

import javax.rmi.CORBA.Util;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.HTNProblem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.ConditionalEffect;
import fr.uga.pddl4j.util.BitVector;

//This class translates STRIPS to SAS+ variables by generating mutex pairs and constructing mutex cliques
//Based on "Efficient Representations and Conversions of Planning Problems", 2014, Toropila (thesis)
//An alternative approach: "Lifted Fact-Alternating Mutex Groups and Pruned Grounding of Classical Planning Problems", 2020, Fiser (article)
//Both approaches rely on the same H(n) heuristic and the concepts introduced by Helmert in 2009
//performance-wise they seem to be the same. I stick with the thesis, because the results seem to be more rigurously evaluated

//The SAS+ translation consists of two parts
//First generating mutex pairs via h2 heuristic (using Bellman-Ford algorithm)
//Then we construct mutex cliques
//And finally we identify cliques with the biggest covering
//TODO: THE Algorithm works for SEQUENTIAL planning. Will eventually need to rewrite it to work with parallel planning

public class Strips2SasPlus {
    //heuristic table contains atom weights
    static HashMap<Collection<Integer>,Integer> heuristicTable = new HashMap<Collection<Integer>, Integer>();
    static List<Collection<Integer>> sets = new ArrayList<>(); //all mutex sets
    static List<Collection<Integer>> cliques = new ArrayList<>(); //all mutex sets
    static HashMap<Integer, Integer> fluent2Clique = new HashMap<Integer, Integer>(); //maps fluent to corresponding clique. i.e.key corresponds to fluent index in PDDL4J. Value corresponds to the clique that the fluent belongs to
    //TODO cliques and fluent2Clique are a bit redundant. May be interesting to remove cliques variable. But then again, sometimes I need to quickly find the fluents that belong to some clique, and other times I need to quickly find to which clique a particular fluent belongs to.

    
    public static long timeout = 60000;//force termination in 1 minute
    public static int fVal = 150; 

    //PART 1
    //Mutex pairs identification via h(2) heuristic
    //SEQUENTIAL PLANNING ONLY!!!!!
    //----------------------------

    static void initialize_heuristicTable(HTNProblem problem) {
        heuristicTable.clear();
        sets.clear();
        cliques.clear();
        

        for (int i = 0; i < problem.getFluents().size(); i++) {


            //PERSONAL MODIFICATION: first check if fluent 
            boolean atom1_inIS = problem.getInitialState().getPositiveFluents().get(i);
            //if atom 1 in initial state - its weight = 0, else = infinity
            
            Set<Integer> col= Collections.unmodifiableSet(
                new HashSet<>(Arrays.asList(i)));
            if (atom1_inIS) {
                heuristicTable.put(col, 0);
            } else {
                heuristicTable.put(col, Integer.MAX_VALUE);
            }

            //if pair(atom1, atom2) in initial state - its weight = 0, else = infinity
            for (int j = i + 1; j < problem.getFluents().size(); j++) {
                boolean atom2_inIS = problem.getInitialState().getPositiveFluents().get(j);
                Set<Integer> col2 = Collections.unmodifiableSet(
                    new HashSet<>(Arrays.asList(i,j)));
                if (atom1_inIS && atom2_inIS /*|| f1.getSymbol() != f2.getSymbol()*/) {
                    heuristicTable.put(col2, 0);
                } else {
                    heuristicTable.put(col2, Integer.MAX_VALUE);
                }
            }
        }
    }

    static boolean change_registered = true;
    static void callH2Hheuristic(HTNProblem problem) {
        //first populate heuristic table with weight values
        initialize_heuristicTable(problem);
        //repeat a loop until no change is identified
        System.out.println("h2 heuristic. Entering while loop");
        while (change_registered) {
            change_registered = false;
            for (Action a : problem.getActions()) { 
                //evaluate action preconditions
                List<Integer> pre = new ArrayList<Integer>();
                BitVector bv = a.getPrecondition().getPositiveFluents();
                for (int i = bv.nextSetBit(0); i >= 0; i = bv.nextSetBit(i + 1)) {
                    pre.add(i);
                }
                int cost1 = eval(pre, problem);
                //check positive/negative effects
                //TODO: DOES NOT SUPPORT CONDITIONAL EFFECTS
                bv = a.getUnconditionalEffect().getPositiveFluents();
                List<Integer> add = new ArrayList<Integer>();
                for (int i = bv.nextSetBit(0); i >= 0; i = bv.nextSetBit(i + 1)) {
                    add.add(i);
                }
                //for each atom p added by action a
                for (int p : add) {
                    //update single atoms added by action a

                    int tmpV;
                    if (cost1 == Integer.MAX_VALUE) {
                        tmpV = cost1;
                    } else {
                        tmpV = cost1 + actionCost(a);
                    }Set<Integer> pCol = Collections.unmodifiableSet(
                        new HashSet<>(Arrays.asList(p)));
                    update(pCol, tmpV);
                    
                    //update pairs of atoms added by action a
                    for (int q : add) {
                        if (q != p) {
                           
                            
                            if (cost1 == Integer.MAX_VALUE) {
                                tmpV = cost1;
                            } else {
                                tmpV = cost1 + actionCost(a);
                            }
                            Set<Integer> p_qCol = Collections.unmodifiableSet(
                                new HashSet<>(Arrays.asList(p,q)));
                            update(p_qCol, tmpV);
                            

                        }
                    }
                    //update atom pairs with p added by a and r by persistance
                    BitVector bv_prime = a.getUnconditionalEffect().getNegativeFluents();
                    List<Integer> persist = new ArrayList<Integer>();
                    for (int i = 0; i < problem.getFluents().size(); i++) {
                        if (!bv_prime.get(i)) {
                            persist.add(i);
                        }
                    }
                    //note - we're not using nextClearBit to find fluents not deleted by action, because nextClearBit 
                    //enters a loop for some reason
                    /*for (int i = bv_prime.nextClearBit(0); i >= 0; i = bv_prime.nextClearBit(i + 1)) {
                        System.out.println("t4 i = "+i + " of "+problem.getFluents().size()+" fluents | bv_prime(size) = "+ bv_prime.length());
                        persist.add(i);
                    }*/
                    for (int r : persist) {
                        if (r != p) {
                            //the already computed cost1 = h(pre(a)) can be used to speed up computation of cost2                       
                            List<Integer> union = new ArrayList<Integer>();
                            union.addAll(pre);
                            union.add(r);
                            int cost2 = eval(union, problem);
                            
                            if (cost2 == Integer.MAX_VALUE) {
                                tmpV = cost2;
                            } else {
                                tmpV = cost2 + actionCost(a);
                            }Set<Integer> p_rCol = Collections.unmodifiableSet(
                                new HashSet<>(Arrays.asList(p,r)));
                                update(p_rCol, tmpV);
                            
                        }
                    }

                }

            }
        }
    }

    //NOTE: at least for now action costs are 1, as they are declared in the paper. MAYBE will be changed later
    static int actionCost(Action a) {
        return 1;
    }

    static boolean update(Collection<Integer> key, int value) {
        
        if (heuristicTable.get(key) > value ) {
            heuristicTable.replace(key, value);
            change_registered = true;
            return true;
        }
        return false;
    }
    
    
    //state evaluation function for the h2 heuristic
    static int eval(List<Integer> atoms, HTNProblem problem) {
        int val = 0;
        for (int i = 0; i < atoms.size(); i++) {Set<Integer> col = Collections.unmodifiableSet(
            new HashSet<>(Arrays.asList(atoms.get(i))));
            val = Math.max(val, heuristicTable.get(col));
            for (int j = i + 1; j < atoms.size(); j++) {
                Set<Integer> col2 = Collections.unmodifiableSet(
            new HashSet<>(Arrays.asList(atoms.get(i),atoms.get(j))));
              
                    val = Math.max(val, heuristicTable.get(col2));
                }
        }

        return val;
    }
    //PART 2
    //Generating mutex sets using a probabilistic algorithm
    //----------------------------
    //per paper, k = 150 * num_of_facts 
    //TODO: ADD TIMEOUT. Meaning, while loop ends either when we have k mutexSets, or timeout is reached
    public static void createFactSets(HTNProblem problem) {
        int k = fVal * problem.getFluents().size();
        List<Collection<Integer>> mutexSets = new ArrayList<>();

        long startTime = System.currentTimeMillis();
        long currentTime = System.currentTimeMillis();

        //first create original list of facts (for the random permutation)
        List<Integer> list = new ArrayList<Integer>();
        for (int i = 0; i < problem.getFluents().size(); i++) {
            
            if(checkFluentNotStatic(i, problem)){
                list.add(i);
            }
        }

        while (mutexSets.size() < k && currentTime - startTime < timeout) {
            //create a random permutation of candidate facts
            java.util.Collections.shuffle(list);
            Stack<Integer> candidates = new Stack<Integer>();
            candidates.addAll(list);
            List<Integer> newSet = new ArrayList<>();

            //until all candidates have been evaluated
            //System.out.println(candidates);
            while (candidates.size() > 0) {
                //pop first candidate
                int candidateFact = candidates.pop();
                //add candidate to set
                newSet.add(candidateFact);
                //filter out all candidates nonmutex with the popped candidate
                for (Iterator<Integer> it = candidates.iterator(); it.hasNext();) {
                    Integer candTmp = it.next();
                    Set<Integer> key = Collections.unmodifiableSet(
                            new HashSet<>(Arrays.asList(candTmp, candidateFact)));
                    if (candidateFact == candTmp) {
                        it.remove();
                    } else if (heuristicTable.get(key) != Integer.MAX_VALUE) {
                        it.remove();
                    }
                }

            }
            //System.out.println(newSet);
            mutexSets.add(newSet);
            currentTime = System.currentTimeMillis();
        }
        sets = mutexSets;
    }
    //PART 3
    //Create mutex cliques that cover facts exactly once
    //----------------------------
    static void greedyCovering(HTNProblem problem) {
        HashSet<Integer> uncovered = new HashSet<>();
        for (int i = 0; i < problem.getFluents().size(); i++) {
            if (checkFluentNotStatic(i, problem)) {
                uncovered.add(i);
            }
        }
        boolean changed = true;
        while (uncovered.size() > 0) {
            System.out.println("while uncovered.size > 0 : " + uncovered.size());
            //first find a the biggest set
            int maxCardinalityIndex = 0;
            //TODO: CURRENTLY I DO FOR LOOP TO FIND SET WITH MAX CARDINALITY. THIS FOR LOOP IS REPEATED UNTIL I HAVE COVERED ALL FACTS. INSTEAD, I SHOULD SORT sets IN ORDER OF DESCENDING CARDINALITY ONCE, AND THEN JUST POP FIRST CHILD DURING EVERY SUBSEQUENT ITERATION. 
            //NOTE: won't work, because cardinality is modified in the next step (remove elements appearing in chosen set)

            for (int i = 0; i < sets.size(); i++) {
                if (sets.get(i).size() > sets.get(maxCardinalityIndex).size()) {
                    maxCardinalityIndex = i;

                }
            }
            List<Integer> chosenSet = new ArrayList<Integer>(sets.get(maxCardinalityIndex));
            sets.remove(maxCardinalityIndex);
            System.out.println("s 1 " + maxCardinalityIndex);
            //remove all facts of chosenSet from unocvered
            for (Integer fact : chosenSet) {
                uncovered.remove(fact);

            }
            System.out.println("s 2 " + chosenSet.size());
            //remove all facts of chosenSet from other mutex sets
            for (int i = 0; i < sets.size(); i++) {
                for (Integer fact : chosenSet) {
                    sets.get(i).remove(fact);

                }
            }
            System.out.println("s 3 " + sets.size());
            //by default, chosen set contains mutex pairs that include static facts. We need to filter out static facts
            //TODO: currently we filter static facts post-factum, while still wasting time constructing mutex pairs that include them. May be better to rewrite the H2 heuristic, so that we ignore the static facts completely

            List<Integer> chosenSetFiltered = new ArrayList<>();
            for (Integer fact : chosenSet) {
                if (checkFluentNotStatic(fact, problem)) {
                    chosenSetFiltered.add(fact);
                    fluent2Clique.put(fact, cliques.size());
                }
            }

            System.out.println("s 4");
            if (!chosenSetFiltered.isEmpty()) {
                cliques.add(chosenSetFiltered);

            }

        }

    }
    
     //verifies if the fluent in question has a possibility to change somewhere
     static List<Boolean> fluentIsStatic = new ArrayList<Boolean>();

     public static boolean checkFluentNotStatic(int i, HTNProblem problem) {
         //initialize the table with values for all fluents at the VERY FIRST call to this function during the app lifetime
         
         if (fluentIsStatic.isEmpty()) {
             for (Fluent f : problem.getFluents()) {
                 boolean isUsedSomewhere = false;
         
                 for (Action a : problem.getActions()) {
                     if (fluentIsUsedByAction(a, f, problem)) {
                         isUsedSomewhere = true;
                         break;
                     }
                 }
                 fluentIsStatic.add(!isUsedSomewhere);
             }
         }
         //when the table is initialized, this function just looks up values in the said table
         return !fluentIsStatic.get(i);
     }

     
     public static boolean fluentIsUsedByAction(Action a, Fluent f, HTNProblem problem) {

        if (a.getUnconditionalEffect().getNegativeFluents()
                .get(problem.getFluents().indexOf(f))
                || a.getUnconditionalEffect().getPositiveFluents()
                        .get(problem.getFluents().indexOf(f))) {
            return true;
        } else {
            for (ConditionalEffect e : a.getConditionalEffects()) {
                if (e.getEffect().getNegativeFluents()
                        .get(problem.getFluents().indexOf(f))
                        || e.getEffect().getPositiveFluents()
                                .get(problem.getFluents().indexOf(f))) {
                    return true;
                }
            }
        }
        return false;
    }
    
    //----------------------------
}
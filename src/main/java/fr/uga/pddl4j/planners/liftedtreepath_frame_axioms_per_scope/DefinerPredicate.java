package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Vector;

public class DefinerPredicate {

    String predicateName;
    ArrayList<String> typesParamPredicate;
    // Map the parameters of the LFG to the set of LiftedFlow that define it
    // HashMap<LiftedFlow, HashSet<LiftedFlow>> lastDefinersPredicateForLiftedFlow;
    HashSet<LiftedFlow> lastDefinersPredicateForLiftedFlow;

    ArrayList<ArrayList<String>> allObjectsPossibleForEachParams;

    public DefinerPredicate(String predicateName, ArrayList<String> typesParamPredicate, Map<String, Vector<String>> dictTypeToObjects, Map<String, HashSet<String>> dictTypeToChildTypes) {
        this.predicateName = predicateName;
        this.typesParamPredicate = typesParamPredicate;
        this.lastDefinersPredicateForLiftedFlow = new HashSet<LiftedFlow>();
        this.allObjectsPossibleForEachParams = new ArrayList<ArrayList<String>>();

        // Find all the object possible for each parameter
        for (String typeParam : this.typesParamPredicate) {
            ArrayList<String> allObjectsPossibleForParam = new ArrayList<String>();
            allObjectsPossibleForParam.addAll(dictTypeToObjects.get(typeParam));

            // Add as well all the child types
            for (String childType : dictTypeToChildTypes.get(typeParam)) {
                allObjectsPossibleForParam.addAll(dictTypeToObjects.get(childType));
            }
                
            allObjectsPossibleForEachParams.add(allObjectsPossibleForParam);
        }
    }

    public DefinerPredicate(DefinerPredicate definerPredicate) {
        this.predicateName = definerPredicate.predicateName;
        // this.typesParamPredicate = new ArrayList<String>();
        // this.typesParamPredicate.addAll(definerPredicate.typesParamPredicate);

        // No need to make a copy for that, it should not change
        this.typesParamPredicate = definerPredicate.typesParamPredicate;


        this.lastDefinersPredicateForLiftedFlow = new HashSet<LiftedFlow>();
        this.lastDefinersPredicateForLiftedFlow.addAll(definerPredicate.lastDefinersPredicateForLiftedFlow);

        // No need to make a copy for that, it should not change
        this.allObjectsPossibleForEachParams = definerPredicate.allObjectsPossibleForEachParams;
    }

    boolean canContainsPredicate(CertifiedPredicate predicate, Map<String, HashSet<String>> dictTypeToParentType) {
        if (predicate.predicateName.equals(this.predicateName)) {
            if (predicate.scope.size() == this.typesParamPredicate.size()) {
                for (int i = 0; i < this.typesParamPredicate.size(); i++) {
                    if (!this.typesParamPredicate.get(i).equals(predicate.typesScope.get(i)) && !dictTypeToParentType.get(predicate.typesScope.get(i)).contains(this.typesParamPredicate.get(i))) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("Definer Predicate:");
        sb.append(this.predicateName + " (");
        for (String typeParam : this.typesParamPredicate) {
            sb.append(typeParam + " ");
        }
        sb.append(")\n");
        sb.append(" Definers: ");
        for (LiftedFlow liftedFlow : this.lastDefinersPredicateForLiftedFlow) {
            if (liftedFlow == null) {
                sb.append("Init_State ");
            } else {
                sb.append(liftedFlow.getUniqueName() + " ");
            }
            
        }

        return sb.toString();
    }
}

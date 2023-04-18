package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

import java.util.ArrayList;
import java.util.HashSet;

import fr.uga.pddl4j.parser.SAS_Plus.AtomCandidate;
import fr.uga.pddl4j.parser.SAS_Plus.AtomVariable;
import fr.uga.pddl4j.parser.SAS_Plus.Candidate;

public class LFGCertifiedPredicate {

    int idLFG;
    Candidate LFG;
    boolean isPositive;
    ArrayList<ScopeVariable> params; // Correspond to the Vi of the LFG
    ArrayList<ScopeVariable> values; // Correspond to the Ci of the LFG (Could be translated into a Integer)
    HashSet<LiftedFlow> certifiers;

    public LFGCertifiedPredicate(int idLFG, Candidate LFG, boolean isPositive, ArrayList<ScopeVariable> params,
            ArrayList<ScopeVariable> values) {
        this.idLFG = idLFG;
        this.LFG = LFG;
        this.isPositive = isPositive;
        this.params = params;
        this.values = values;
        this.certifiers = new HashSet<LiftedFlow>();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        if (!this.isPositive) {
            sb.append("NOT ");
        }

        sb.append(this.LFG.getUniqueStringRepresentation() + ": ");
        sb.append("Params: ");
        for (ScopeVariable param : this.params) {
            sb.append(param.getUniqueName() + " (" + param.getType() + ") ");
        }

        if (isPositive) {
            sb.append("Values: ");
            for (ScopeVariable value : this.values) {
                if (value == null) {
                    sb.append("null ");
                } else {
                    sb.append(value.getUniqueName() + " (" + value.getType() + ") ");
                }
            }
        }
        return sb.toString();
    }

    /**
     * The definer LFG key, correspond to all the parameters of the LFG where each parameter is
     * a string. We must do a recursive call to get all the parameters of the LFG.
     * @return
     */
    public HashSet<String> getAllDefinerLFGKey() {
        HashSet<String> result = new HashSet<String>();
        recursiveGetAllDefinerLFGKey(result, new ArrayList<String>(), 0);
        return result;
    }

    private void recursiveGetAllDefinerLFGKey(HashSet<String> result, ArrayList<String> currentKey, int idxParam) {
        if (currentKey.size() == this.params.size()) {
            result.add(DefinerLFG.convertParamsStringLFGToKey(currentKey));
            return;
        }

        // // First, add null to the current key
        // currentKey.add(null);
        // // Recursive call
        // recursiveGetAllDefinerLFGKey(result, currentKey, idxParam + 1);
        // // Remove element from the current key
        // currentKey.remove(currentKey.size() - 1);

        // Get the current variable
        ScopeVariable scopeVar = this.params.get(idxParam);

        // For all values that can be taken by this scope variable
        for (String value : scopeVar.getPossibleValueVariable()) {
            // Add element to the current key
            currentKey.add(value);
            // Recursive call
            recursiveGetAllDefinerLFGKey(result, currentKey, idxParam + 1);
            // Remove element from the current key
            currentKey.remove(currentKey.size() - 1);
        }
    }

    // TODO Can this function could return multiple LFGCertifiedPredicate?
    static public HashSet<LFGCertifiedPredicate> generateLFGCertifiedPredFromPredAndScope(String predicateName,
            ArrayList<ScopeVariable> scopeVariables, ArrayList<Candidate> liftedFamGroups, boolean isPositive) {


        HashSet<LFGCertifiedPredicate> result = new HashSet<LFGCertifiedPredicate>();

        // Find all the lifted fam groups which contains it
        for (Candidate liftedFamGroup : liftedFamGroups) {
            // Check if this lifted fam group can contains this predicate
            for (AtomCandidate atomCandidate : liftedFamGroup.mutexGroup) {
                if (!atomCandidate.predSymbolName.equals(predicateName)) {
                    continue;
                }

                // Check if the parameters of the predicate are the same
                boolean isSameParam = true;
                for (int i = 0; i < atomCandidate.paramsId.size(); i++) {
                    String paramTypeAtomCandidate = liftedFamGroup.variables
                            .get(atomCandidate.paramsId.get(i)).typeName;
                    String paramTypeFluent = scopeVariables.get(i).getType();
                    if (!paramTypeAtomCandidate.equals(paramTypeFluent)) {
                        isSameParam = false;
                        break;
                    }
                }
                if (!isSameParam) {
                    continue;
                }

                // Else create the certified predicate associated to this initial predicate
                ArrayList<ScopeVariable> params = new ArrayList<ScopeVariable>();
                ArrayList<ScopeVariable> values = new ArrayList<ScopeVariable>();

                // Reiterate over the parameters of the lifted fam group to set param and values
                for (int paramId = 0; paramId < liftedFamGroup.variables.size(); paramId++) {
                    AtomVariable var = liftedFamGroup.variables.get(paramId);
                    // Check if the atom candidate contains this variable
                    if (atomCandidate.paramsId.contains(paramId)) {
                        int idxParam = atomCandidate.paramsId.indexOf(paramId);
                        // Get the object associated to this parameter
                        ScopeVariable scopeVar = scopeVariables.get(idxParam);

                        // Add it into the param if it is not a counted variable
                        // If it is a counted variable, then add it into the values
                        if (var.isCountedVar) {
                            values.add(scopeVar);
                        } else {
                            params.add(scopeVar);
                        }
                    } else {
                        // Add null into the param if it is not a counted variable
                        // If it is a counted variable, then add it into the values
                        if (var.isCountedVar) {
                            values.add(null);
                        } else {
                            params.add(null);
                        }
                    }
                }

                // Create our lifted fam group predicate
                LFGCertifiedPredicate lfgCertifiedPredicate = new LFGCertifiedPredicate(0, liftedFamGroup, isPositive,
                        params, values);
                // Add it into the list of lifted fam group predicate
                // System.out.println("Conversion from predicate: " + prettyNameFluentInit + "
                // to " + lfgCertifiedPredicate);
                result.add(lfgCertifiedPredicate);
                break;
            }
        }

        // TODO add a special lifted fam group in this case where all arguments are Vi
        // and there are no values
        if (result.size() == 0) {
            System.out.println("Cannot find a lifted fam group for predicate: " + predicateName);
            // System.exit(1);
            // return null;
            return result;
        }
        return result;
    }

}

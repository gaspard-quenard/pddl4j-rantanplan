package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import fr.uga.pddl4j.parser.SAS_Plus.Candidate;

public class DefinerLFG {

    Candidate LFG;
    // Map the parameters of the LFG to the set of LiftedFlow that define it
    Map<String, HashSet<LiftedFlow>> lastDefinersLFG;

    public DefinerLFG(Candidate LFG) {
        this.LFG = LFG;
        this.lastDefinersLFG = new HashMap<String, HashSet<LiftedFlow>>();
    }

    public DefinerLFG(DefinerLFG source) {
        this.LFG = source.LFG;
        this.lastDefinersLFG = new HashMap<String, HashSet<LiftedFlow>>();
        for (String key : source.lastDefinersLFG.keySet()) {
            this.lastDefinersLFG.put(key, new HashSet<LiftedFlow>(source.lastDefinersLFG.get(key)));
        }
    }


    public String convertParamsLFGToKey(ArrayList<ScopeVariable> paramsLFG) {
        if (paramsLFG.size() == 0) {
            return "NONE";
        }
        StringBuilder sb = new StringBuilder();
        for (ScopeVariable paramLFG : paramsLFG) {
            sb.append(paramLFG.getUniqueName() + "_");
        }
        // Remove the last _
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }

    public static String convertParamsStringLFGToKey(ArrayList<String> paramsStringLFG) {
        if (paramsStringLFG.size() == 0) {
            return "NONE";
        }
        StringBuilder sb = new StringBuilder();
        for (String paramLFG : paramsStringLFG) {
            sb.append(paramLFG + "%");
        }
        // Remove the last _
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }

    public void addOrUpdateParamsLFG(ArrayList<ScopeVariable> paramsLFG, LiftedFlow lf) {

        HashSet<String> allKeysThatWillBeUpdates = getAllDefinerLFGKey(paramsLFG);
        
        for (String key : allKeysThatWillBeUpdates) {
            if (this.lastDefinersLFG.containsKey(key)) {
                // Clear all the previous LiftedFlow that define the same parameters
                this.lastDefinersLFG.get(key).clear();
                this.lastDefinersLFG.get(key).add(lf);
            } else {
                HashSet<LiftedFlow> set = new HashSet<LiftedFlow>();
                set.add(lf);
                this.lastDefinersLFG.put(key, set);
            }
        }
    }

    public void mergeDefinerLFG(DefinerLFG otherDefiner) {
        for (String key : otherDefiner.lastDefinersLFG.keySet()) {
            if (this.lastDefinersLFG.containsKey(key)) {
                this.lastDefinersLFG.get(key).addAll(otherDefiner.lastDefinersLFG.get(key));
            } else {
                this.lastDefinersLFG.put(key, new HashSet<LiftedFlow>(otherDefiner.lastDefinersLFG.get(key)));
            }
        }
    }


    public HashSet<String> getAllDefinerLFGKey(ArrayList<ScopeVariable> params) {
        HashSet<String> result = new HashSet<String>();
        recursiveGetAllDefinerLFGKey(params, result, new ArrayList<String>(), 0);
        return result;
    }

    private void recursiveGetAllDefinerLFGKey(ArrayList<ScopeVariable> params, HashSet<String> result, ArrayList<String> currentKey, int idxParam) {
        if (currentKey.size() == params.size()) {
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
        ScopeVariable scopeVar = params.get(idxParam);

        // For all values that can be taken by this scope variable
        for (String value : scopeVar.getPossibleValueVariable()) {
            // Add element to the current key
            currentKey.add(value);
            // Recursive call
            recursiveGetAllDefinerLFGKey(params, result, currentKey, idxParam + 1);
            // Remove element from the current key
            currentKey.remove(currentKey.size() - 1);
        }
    }


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("Definer LFG:");
        sb.append(this.LFG.getUniqueStringRepresentation() + ": ");
        for (String key : this.lastDefinersLFG.keySet()) {
            sb.append("\n    Params: " + key + " Definers: ");
            for (LiftedFlow lf : this.lastDefinersLFG.get(key)) {
                sb.append(lf.getUniqueName() + " ");
            }
        }
        return sb.toString();
    }
}

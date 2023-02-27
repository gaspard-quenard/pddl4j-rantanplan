package fr.uga.pddl4j.planners.liftedtreepath_smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;


public class ScopeVariable {

    static int numScopeVariable;

    private int uniqueId;
    private String typeVariable;
    private HashSet<String> possibleValueVariable;

    // We want to have constrains of the style:
    // SCOPE_3 == SCOPE_1 => (SCOPE_5 = SCOPE_7) and (SCOPE_8 = SCOPE_9)
    // For this example, SCOPE_3 is the current scope variable object
    // SCOPE_1 is the key of the constrains, and (SCOPE_5, SCOPE_7 ) is our 
    // first doubleScopeVariable, (SCOPE_8, SCOPE_9) is our second doubleScopeVariable.
    // We also want to knwo which lifted flow has incurred this constrains
    private ArrayList<ConstrainsOnScopeVariable> allConstrainsOnScopeVariables;


    // Just a list which indicate all the scope variable that must be differents from this scope variable
    private HashSet<ScopeVariable> scopeVarThatMustBeDifferentFromMe;

    public ScopeVariable() {
        this.typeVariable = null;
        this.possibleValueVariable = new HashSet<String>();

        this.uniqueId = ScopeVariable.numScopeVariable;
        ScopeVariable.numScopeVariable++;

        this.allConstrainsOnScopeVariables = new ArrayList<>();

        this.scopeVarThatMustBeDifferentFromMe = new HashSet<>();
    }

    public void addTypeVariable(String typeVariable) {
        this.typeVariable = typeVariable;
    }

    public void addConstrainsOnScopeVariable(ScopeVariable pivot, LiftedFlow flowWhichHaveCausedThisConstrains, ScopeVariable scopeVar1, ScopeVariable scopeVar2, HashSet<ScopeVariable> constrainsOnPivot ) {
        for (ConstrainsOnScopeVariable constrainsOnScopeVariable : this.allConstrainsOnScopeVariables) {
            if (constrainsOnScopeVariable.pivot.equals(pivot)) {
                // Check if we already have the lifted flow for this constrains
                int idx = constrainsOnScopeVariable.liftedFlows.indexOf(flowWhichHaveCausedThisConstrains);
                if (idx == -1) {
                    // Add the lifted flow 
                    constrainsOnScopeVariable.liftedFlows.add(flowWhichHaveCausedThisConstrains);
                    // Add as well the pair for this lifted flow
                    HashSet<Pair<ScopeVariable, ScopeVariable>> hashSetpair =  new HashSet<Pair<ScopeVariable, ScopeVariable>>();
                    if (scopeVar1 != null && scopeVar2 != null) {
                        hashSetpair.add(Pair.of(scopeVar1, scopeVar2));
                        constrainsOnScopeVariable.pairsScopeThatMustBeEquals.add(hashSetpair);
                    }
                    // Add as well the constrains on the pivot
                    if (constrainsOnPivot != null) {
                        constrainsOnScopeVariable.constrainsOnPivot.addAll(constrainsOnPivot);
                    }
                    
                    return;

                } else {
                    // Add the pair into the HashSet pair if it does not already exist
                    if (scopeVar1 != null && scopeVar2 != null) {
                        constrainsOnScopeVariable.pairsScopeThatMustBeEquals.get(idx).add(Pair.of(scopeVar1, scopeVar2));
                    }
                    if (constrainsOnPivot != null) {
                        constrainsOnScopeVariable.constrainsOnPivot.addAll(constrainsOnPivot);
                    }
                    
                    return;
                }
            }
        }
        // If we do not have found this pivot for this scope var, add it
        ConstrainsOnScopeVariable constrains = new ConstrainsOnScopeVariable();
        constrains.pivot = pivot;
        constrains.liftedFlows.add(flowWhichHaveCausedThisConstrains);
        if (scopeVar1 != null && scopeVar2 != null) {
            HashSet<Pair<ScopeVariable, ScopeVariable>> hashSetpair =  new HashSet<Pair<ScopeVariable, ScopeVariable>>();
            hashSetpair.add(Pair.of(scopeVar1, scopeVar2));
            constrains.pairsScopeThatMustBeEquals.add(hashSetpair);
        }
        
        if (constrainsOnPivot != null) {
            constrains.constrainsOnPivot.addAll(constrainsOnPivot);
        }
        
        this.allConstrainsOnScopeVariables.add(constrains);
        return;
    }

    public void addConstrainsNotEqual(ScopeVariable scopeVariable) {
        this.scopeVarThatMustBeDifferentFromMe.add(scopeVariable);
    }

    public HashSet<ScopeVariable> getConstrainsNotEqual() {
        return this.scopeVarThatMustBeDifferentFromMe;
    }

    public ArrayList<ConstrainsOnScopeVariable> getConstrains() {
        return this.allConstrainsOnScopeVariables;
    }

    public void addValueToScope(String value) {
        this.possibleValueVariable.add(value);
    }

    public HashSet<String> getPossibleValueVariable() {
        return this.possibleValueVariable;
    }

    public String getType() {
        return this.typeVariable;
    }

    public boolean isConstant() {
        return this.possibleValueVariable.size() == 1;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(this.getUniqueName() + ": ");
        sb.append("<" + this.typeVariable + "> ");
        if (!this.isConstant()) {
            sb.append(" { ");
            for (String value : this.possibleValueVariable) {
                sb.append(value + " ");
            }
            sb.append("}");
        }
        return sb.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (!ScopeVariable.class.isAssignableFrom(obj.getClass())) {
            return false;
        }
        final ScopeVariable other = (ScopeVariable) obj;
        if (this.uniqueId != other.uniqueId) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        return this.uniqueId;
    }

    public String getUniqueName() {
        if (this.isConstant()) {
            Iterator<String> it = this.possibleValueVariable.iterator();
            return it.next();
        } else {
            return "SCOPE_" + uniqueId;
        }

    }
}


class ConstrainsOnScopeVariable {

    ScopeVariable pivot;
    HashSet<ScopeVariable> constrainsOnPivot; // The pivot should not be equal to any of these scopeVariable
    ArrayList<LiftedFlow> liftedFlows; // LiftedFlow that will be bound by this constrains
    ArrayList<HashSet<Pair<ScopeVariable, ScopeVariable>>> pairsScopeThatMustBeEquals;

    public ConstrainsOnScopeVariable() {
        this.liftedFlows = new ArrayList<LiftedFlow>();
        this.constrainsOnPivot = new HashSet<ScopeVariable>();
        this.pairsScopeThatMustBeEquals = new ArrayList<HashSet<Pair<ScopeVariable, ScopeVariable>>>();
    }

}
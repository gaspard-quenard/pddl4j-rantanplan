package fr.uga.pddl4j.planners.liftedtreepath_smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class CertifiedPredicate {

    // Name of the predicate
    String predicateName;

    // Positive or negative predicate
    boolean isPositive = true;

    // Scope of each value of the predicate
    ArrayList<ScopeVariable> scope;

    // Ensemble of node which can certified this predicate
    HashSet<LiftedFlow> certifiers;

    // An array which indicate the type of each scope variable of the ceritified predicate
    ArrayList<String> typesScope;

    // Constrains on the scope. We want some scope to not have the value of other scopes
    Map<ScopeVariable, HashSet<ScopeVariable>> inputConstrainsScope;
    Map<ScopeVariable, HashSet<ScopeVariable>> outputConstrainsScope;

    public CertifiedPredicate(String predicateName, boolean isPositive, ArrayList<ScopeVariable> scope,
            LiftedFlow certifier) {

        this.predicateName = predicateName;
        this.isPositive = isPositive;
        this.scope = scope;
        this.certifiers = new HashSet<LiftedFlow>();
        this.certifiers.add(certifier);

        this.inputConstrainsScope = new HashMap<ScopeVariable, HashSet<ScopeVariable>>();
        this.outputConstrainsScope = new HashMap<ScopeVariable, HashSet<ScopeVariable>>();

        this.typesScope = new ArrayList<String>();
        for (int i = 0; i < this.scope.size(); i++) {
            this.typesScope.add(this.scope.get(i).getType());
        }
    }

    public CertifiedPredicate(String predicateName, boolean isPositive, ArrayList<ScopeVariable> scope,
            HashSet<LiftedFlow> certifiers) {

        this.predicateName = predicateName;
        this.isPositive = isPositive;
        this.scope = scope;
        this.certifiers = new HashSet<LiftedFlow>();
        this.certifiers.addAll(certifiers);

        this.typesScope = new ArrayList<String>();
        for (int i = 0; i < this.scope.size(); i++) {
            this.typesScope.add(this.scope.get(i).getType());
        }

        this.inputConstrainsScope = new HashMap<ScopeVariable, HashSet<ScopeVariable>>();
        this.outputConstrainsScope = new HashMap<ScopeVariable, HashSet<ScopeVariable>>();
    }

    public void setConstrainsScope(Map<ScopeVariable, HashSet<ScopeVariable>> constrains) {
        for (ScopeVariable var : constrains.keySet()) {
            if (!this.inputConstrainsScope.containsKey(var)) {
                this.inputConstrainsScope.put(var, new HashSet<>());
            }
            for (ScopeVariable constrain : constrains.get(var)) {
                this.inputConstrainsScope.get(var).add(constrain);    
            }
            if (!this.outputConstrainsScope.containsKey(var)) {
                this.outputConstrainsScope.put(var, new HashSet<>());
            }
            for (ScopeVariable constrain : constrains.get(var)) {
                this.outputConstrainsScope.get(var).add(constrain);    
            }
        }
    }

    public void addOutputConstrains(ScopeVariable key, ScopeVariable constrainsToAdd) {
        if (!this.outputConstrainsScope.containsKey(key)) {
            this.outputConstrainsScope.put(key, new HashSet<>());
        }
        this.outputConstrainsScope.get(key).add(constrainsToAdd);
    }

    /**
     * Check if this predicate is opposite to another predicate.
     * Two predicates are opposite if they have the same name and scope, but
     * different isPositive values.
     * 
     * @param other The other predicate to compare with.
     * @return True if this predicate is opposite to the other predicate, False
     *         otherwise.
     */
    public boolean isOppositeTo(CertifiedPredicate other) {
        return this.predicateName.equals(other.predicateName)
                && this.scope.equals(other.scope)
                && this.isPositive != other.isPositive;
    }

    /**
     * Check if this predicate is equal to another predicate.
     * Two predicates are equal if they have the same name and scope and same isPositive values
     * 
     * @param other The other predicate to compare with.
     * @return True if this predicate is equal to the other predicate, False
     *         otherwise.
     */
    public boolean isEqualsTo(CertifiedPredicate other) {
        return this.predicateName.equals(other.predicateName)
                && this.scope.equals(other.scope)
                && this.isPositive == other.isPositive;
    }

    public boolean isEqualOrOppositeTo(CertifiedPredicate other) {
        return this.predicateName.equals(other.predicateName) && this.scope.equals(other.scope);
    }

    @Override
    public String toString() {
        StringBuilder certifiedPredToDisplay = new StringBuilder();
        certifiedPredToDisplay.append("Certified Pred [");
        if (!this.isPositive) {
            certifiedPredToDisplay.append("not ");
        }
        certifiedPredToDisplay.append(this.predicateName);
        for (int i = 0; i < this.scope.size(); i++) {
            certifiedPredToDisplay.append(" " +  this.scope.get(i));
        }

        if (this.inputConstrainsScope.keySet().size() > 0) {
            certifiedPredToDisplay.append("( input constrains: ");
            for (ScopeVariable scopeVarConstrains : this.inputConstrainsScope.keySet()) {
                certifiedPredToDisplay.append(scopeVarConstrains.getUniqueName() + " != { ");
                for (ScopeVariable constrains : this.inputConstrainsScope.get(scopeVarConstrains)) {
                    certifiedPredToDisplay.append(constrains.getUniqueName() + " ");
                }
                certifiedPredToDisplay.append("} ");
            }
            certifiedPredToDisplay.append(") ");
        }
        if (this.outputConstrainsScope.keySet().size() > 0) {
            certifiedPredToDisplay.append("( output constrains: ");
            for (ScopeVariable scopeVarConstrains : this.outputConstrainsScope.keySet()) {
                certifiedPredToDisplay.append(scopeVarConstrains.getUniqueName() + " != { ");
                for (ScopeVariable constrains : this.outputConstrainsScope.get(scopeVarConstrains)) {
                    certifiedPredToDisplay.append(constrains.getUniqueName() + " ");
                }
                certifiedPredToDisplay.append("} ");
            }
            certifiedPredToDisplay.append(") ");
        }


        certifiedPredToDisplay.append("]");

        return certifiedPredToDisplay.toString();
    }
}

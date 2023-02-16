package fr.uga.pddl4j.planners.lilotane;

import java.util.ArrayList;

public class PseudoFact {
    
    private String predicateName;

    private boolean isPositive;

    private int layer;
    private int layerElement;
    private boolean isGroundFact = true;

    private ArrayList<ScopeVariable> scopeVariables;

    public PseudoFact(String _predicateName, int layer, int layerElm) {
        this.predicateName = _predicateName;
        this.isPositive = true;
        this.scopeVariables = new ArrayList<ScopeVariable>();
        this.layer = layer;
        this.layerElement = layerElm;
    }

    public void setIsPositive(boolean _isPositive) {
        this.isPositive = _isPositive;
    }

    public boolean isPositive() {
        return this.isPositive;
    }

    public void addScopeVariable(ScopeVariable scopeVariable) {
        this.scopeVariables.add(scopeVariable);
        if (scopeVariable.getPossibleValueVariable().size()> 1) {
            this.isGroundFact = false;
        }
    }

    public String getPredicateName() {
        return this.predicateName;
    }

    public ArrayList<ScopeVariable> getScopeVariables() {
        return this.scopeVariables;
    }

    public boolean isGroundFact() {
        return this.isGroundFact;
    }

    public String getUniqueName() {
        StringBuilder sb = new StringBuilder();
        if (this.isGroundFact) {
            sb.append("FLUENT_");
        }
        sb.append(this.predicateName);
        for (ScopeVariable scopeVariable : this.scopeVariables) {
            sb.append("_" + scopeVariable.getUniqueName());
        }
        sb.append("__" + this.layer + "_" + this.layerElement);
        return sb.toString();
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (!this.isPositive) {
            sb.append("not ");
        }
        sb.append(this.predicateName + "(");
        for (ScopeVariable scopeVariable : this.scopeVariables) {
            sb.append(scopeVariable.getUniqueName() + ", ");
        }
        sb.append(")");
        return sb.toString();
    }
}

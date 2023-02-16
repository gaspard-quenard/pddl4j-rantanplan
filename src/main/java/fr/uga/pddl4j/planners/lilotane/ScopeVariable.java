package fr.uga.pddl4j.planners.lilotane;

import java.util.HashSet;
import java.util.Iterator;

public class ScopeVariable {
    static int numScopeVariable;

    private int uniqueId;
    private String typeVariable;
    private HashSet<String> possibleValueVariable;


    public ScopeVariable() {

        this.typeVariable = null;
        this.possibleValueVariable = new HashSet<String>();

        this.uniqueId = ScopeVariable.numScopeVariable;
        ScopeVariable.numScopeVariable++;
    }

    public boolean isConstant() {
        return this.possibleValueVariable.size() == 1;
    }

    public void addTypeVariable(String typeVariable) {
        this.typeVariable = typeVariable;
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

    public void setType(String type) {
        this.typeVariable = type;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (obj == this) {
            return true;
        }
        if (!(obj instanceof ScopeVariable)) {
            return false;
        }
        ScopeVariable other = (ScopeVariable) obj;
        return this.uniqueId == other.uniqueId;
    }

    @Override
    public int hashCode() {
        return this.uniqueId;
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

    public String getUniqueName() {
        if (this.isConstant()) {
            Iterator<String> it = this.possibleValueVariable.iterator();
            return it.next();
        } else {
            return "SCOPE_" + uniqueId;
        }

    }
}

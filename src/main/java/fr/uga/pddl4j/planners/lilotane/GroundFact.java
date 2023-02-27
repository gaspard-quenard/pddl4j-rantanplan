package fr.uga.pddl4j.planners.lilotane;

import java.util.ArrayList;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;

public class GroundFact {

    private String predicateName;

    private boolean isPositive;

    private int layer;
    private int layerElement;

    private ArrayList<String> groundParameters;

    public GroundFact(Problem problem, Fluent f, boolean isPositive, int layer, int layerElement) {

        this.predicateName = problem.getPredicateSymbols().get(f.getSymbol());

        this.groundParameters = new ArrayList<String>();
        for (int fluentArg : f.getArguments()) {
            groundParameters.add(problem.getConstantSymbols().get(fluentArg));
        }

        this.isPositive = true;
        this.layer = layer;
        this.layerElement = layerElement;
    }

    public void setIsPositive(boolean _isPositive) {
        this.isPositive = _isPositive;
    }

    public boolean isPositive() {
        return this.isPositive;
    }

    public String getPredicateName() {
        return this.predicateName;
    }

    public ArrayList<String> getParamters() {
        return this.groundParameters;
    }

    public String getUniqueName() {
        StringBuilder sb = new StringBuilder();
        sb.append("FLUENT_");
        sb.append(this.predicateName);
        for (String parameter : this.groundParameters) {
            sb.append("_" + parameter);
        }
        sb.append("__" + this.layer + "_" + this.layerElement);
        return sb.toString();
    }

    public String toString() {
        return this.getUniqueName();
    }
}

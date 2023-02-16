package fr.uga.pddl4j.planners.lilotane;

import java.util.ArrayList;

import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.Symbol;

public class LiftedMethod {

    static int id = 0;

    private String name;
    private ArrayList<ScopeVariable> parameters;
    private ArrayList<PseudoFact> preconditions;
    private LiftedMethod parentMethod;
    private int layer;
    private int layerElement;
    private int idMethod = LiftedMethod.id++;

    public LiftedMethod(String name, LiftedMethod parentMethod, int layer, int layerElement) {
        this.name = name;
        this.preconditions = new ArrayList<PseudoFact>();
        this.parameters = new ArrayList<ScopeVariable>();
        this.parentMethod = parentMethod;
        this.layer = layer;
        this.layerElement = layerElement;
    }

    public String getName() {
        return this.name;
    }

    public int getLayer() {
        return this.layer;
    }

    public int getLayerElement() {
        return this.layerElement;
    }

    public void addParameter(ScopeVariable parameter) {
        this.parameters.add(parameter);
    }

    public LiftedMethod getParentMethod() {
        return this.parentMethod;
    }

    public ArrayList<ScopeVariable> getParameters() {
        return this.parameters;
    }

    public void addPrecondition(PseudoFact precondition) {
        this.preconditions.add(precondition);
    }

    public ArrayList<PseudoFact> getPreconditions() {
        return this.preconditions;
    }

    public void addPreconditionsFromParsedMethodPreconditions(Expression<String> preconditionsParsedMethod) {
        int numberPreMethod = preconditionsParsedMethod.getChildren().size();
        if (numberPreMethod == 0 && preconditionsParsedMethod.getSymbol() != null) {
            numberPreMethod = 1;
        }

        for (int preId = 0; preId < numberPreMethod; preId++) {

            Expression<String> pre;

            if (numberPreMethod > 1) {
                pre = preconditionsParsedMethod.getChildren().get(preId);
            } else {
                pre = preconditionsParsedMethod;
            }

            if (pre.getConnector().getImage().equals("true")) {
                continue;
            }

            boolean predicateIsPositive = true;

            // Negative predicate
            if (pre.getConnector().getImage().equals("not")) {
                predicateIsPositive = false;
                pre = pre.getChildren().get(0);
            }

            String namePredicate = pre.getSymbol().getValue();

            PseudoFact pseudoFact = new PseudoFact(namePredicate, this.layer, this.layerElement);
            pseudoFact.setIsPositive(predicateIsPositive);

            for (Symbol<String> arg : pre.getArguments()) {
                int idxArg = Integer.parseInt(arg.getValue().substring(2));
                pseudoFact.addScopeVariable(this.getParameters().get(idxArg));
            }

            this.addPrecondition(pseudoFact);
        }
    }

    public String getUniqueName() {
        return "METHOD-" + this.idMethod + "_" + this.name + "__" + this.layer + "_" + this.layerElement;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(this.name + ": ");
        sb.append("Preconditions: ");
        for (PseudoFact precondition : this.preconditions) {
            sb.append(precondition.toString() + ", ");
        }
        return sb.toString();
    }
}

package fr.uga.pddl4j.planners.lilotane;

import java.util.ArrayList;

import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.Symbol;

public class LiftedAction {

    static int id = 0;

    private String name;
    private ArrayList<ScopeVariable> parameters;
    private ArrayList<PseudoFact> preconditions;
    private ArrayList<PseudoFact> effects;
    private LiftedMethod parentMethod;
    private int idAction = LiftedAction.id++;

    boolean isNoopAction = false;

    private int layer;
    private int layerElement;

    public LiftedAction(String name, LiftedMethod parentMethod, int layer, int layerElement) {
        this.name = name;
        this.parameters = new ArrayList<ScopeVariable>();
        this.preconditions = new ArrayList<PseudoFact>();
        this.effects = new ArrayList<PseudoFact>();
        this.parentMethod = parentMethod;
        this.layer = layer;
        this.layerElement = layerElement;
    }

    public LiftedAction(LiftedAction other) {
        this.name = other.getName();
        this.parameters = other.parameters;
        this.preconditions = other.preconditions;
        this.effects = other.effects;
        this.parentMethod = other.parentMethod;
        this.layer = other.layer;
        this.layerElement = other.layerElement;
    }

    // Special blank action used when a method does not have any subtasks
    public LiftedAction(boolean isNoopAction, LiftedMethod parentMethod, int layer, int layerElement) {
        this.isNoopAction = isNoopAction;
        this.name = "NOOP";
        this.parameters = new ArrayList<ScopeVariable>();
        this.preconditions = new ArrayList<PseudoFact>();
        this.effects = new ArrayList<PseudoFact>();
        this.parentMethod = parentMethod;
        this.layer = layer;
        this.layerElement = layerElement;
    }

    public String getName() {
        return this.name;
    }

    public void setLayer(int layer) {
        this.layer = layer;
    }

    public int getLayer() {
        return this.layer;
    }

    public void setLayerElement(int layerElement) {
        this.layerElement = layerElement;
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


    public void addEffect(PseudoFact effect) {
        this.effects.add(effect);
    }

    public ArrayList<PseudoFact> getEffects() {
        return this.effects;
    }

    public void addPreconditionsFromParsedActionPreconditions(Expression<String> preconditionsParsedAction) {
        int numberPreAction = preconditionsParsedAction.getChildren().size();
        if (numberPreAction == 0 && preconditionsParsedAction.getSymbol() != null) {
            numberPreAction = 1;
        }

        for (int preId = 0; preId < numberPreAction; preId++) {

            Expression<String> pre;

            if (numberPreAction > 1) {
                pre = preconditionsParsedAction.getChildren().get(preId);
            } else {
                pre = preconditionsParsedAction;
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


    public void addEffectsFromParsedActionEffects(Expression<String> effectsParsedAction) {
        int numberPreMethod = effectsParsedAction.getChildren().size();
        if (numberPreMethod == 0 && effectsParsedAction.getSymbol() != null) {
            numberPreMethod = 1;
        }

        for (int preId = 0; preId < numberPreMethod; preId++) {

            Expression<String> pre;

            if (numberPreMethod > 1) {
                pre = effectsParsedAction.getChildren().get(preId);
            } else {
                pre = effectsParsedAction;
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

            PseudoFact pseudoFact = new PseudoFact(namePredicate, this.layer, this.layerElement + 1);
            pseudoFact.setIsPositive(predicateIsPositive);

            for (Symbol<String> arg : pre.getArguments()) {
                int idxArg = Integer.parseInt(arg.getValue().substring(2));
                pseudoFact.addScopeVariable(this.getParameters().get(idxArg));
            }

            this.addEffect(pseudoFact);
        }
    }

    public String getUniqueName() {
        return "ACTION-" + this.idAction + "_" + this.name + "__" + this.layer + "_" + this.layerElement;
        // if (this.isNoopAction) {
        //     return "ACTION-" + this.idAction + "_" + "NOOP__" +  this.layer + "_" + this.layerElement;
        // }
        // else {
        //     return "ACTION-" + this.idAction + "_" + this.name + "__" + this.layer + "_" + this.layerElement;
        // }   
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(this.getUniqueName() + ": ");
        sb.append("Preconditions: ");
        for (PseudoFact precondition : this.preconditions) {
            sb.append(precondition.toString() + ", ");
        }
        sb.append("Effects: ");
        for (PseudoFact effect : this.effects) {
            sb.append(effect.toString() + ", ");
        }
        return sb.toString();
    }
}

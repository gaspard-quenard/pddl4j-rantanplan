package fr.uga.pddl4j.planners.lilotane;

public class LilotaneOptimization {

    public boolean useSASplus;
    public boolean useOneVarToEncodeAllActionsAtLayerAndPos;
    public boolean useOneVarToEncodeAllMethodsAtLayerAndPos;

    public LilotaneOptimization(boolean useSASplus, boolean useOneVarToEncodeAllActionsAtLayerAndPos, boolean useOneVarToEncodeAllMethodsAtLayerAndPos) {

        this.useSASplus = useSASplus;
        this.useOneVarToEncodeAllActionsAtLayerAndPos = useOneVarToEncodeAllActionsAtLayerAndPos;
        this.useOneVarToEncodeAllMethodsAtLayerAndPos = useOneVarToEncodeAllMethodsAtLayerAndPos;
    }

    public void displayCurrentUsedOptimizations() {
        System.out.println("Current optimizations used: ");
        System.out.println("SAS+: " + this.useSASplus);
        System.out.println("One var to encode all actions at each layer and position: " + this.useOneVarToEncodeAllActionsAtLayerAndPos);
        System.out.println("One var to encode all methods at each layer and position: " + this.useOneVarToEncodeAllMethodsAtLayerAndPos);
        System.out.println();
    }
}

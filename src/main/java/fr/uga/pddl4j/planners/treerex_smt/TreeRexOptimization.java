package fr.uga.pddl4j.planners.treerex_smt;

public class TreeRexOptimization {

    public boolean useSASplus;
    public boolean useOneVarToEncodeAllActionsAtLayerAndPos;
    public boolean useOneVarToEncodeAllMethodsAtLayerAndPos;

    public TreeRexOptimization(boolean useSASplus, boolean useOneVarToEncodeAllActionsAtLayerAndPos, boolean useOneVarToEncodeAllMethodsAtLayerAndPos) {

        this.useSASplus = useSASplus;
        this.useOneVarToEncodeAllActionsAtLayerAndPos = useOneVarToEncodeAllActionsAtLayerAndPos;
        this.useOneVarToEncodeAllMethodsAtLayerAndPos = useOneVarToEncodeAllMethodsAtLayerAndPos;
    }
}

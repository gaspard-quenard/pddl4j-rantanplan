package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

public class LiftedTreePathConfig {
    // Debug mode
    public static boolean DEBUG = false;

    public static boolean simplifyEffsActionsWithSASPlus = false;
    // Use SAS+ encoding
    public static boolean useSASPlusEncoding = false;
    // Use macro actions
    public static boolean useMacroAction = false;

    LiftedTreePathConfig(boolean debug, boolean simplifyEffsActionsWithSASPlus, boolean useSASPlusEncoding, boolean useMacroAction) {
        LiftedTreePathConfig.DEBUG = debug;
        LiftedTreePathConfig.simplifyEffsActionsWithSASPlus = simplifyEffsActionsWithSASPlus;
        LiftedTreePathConfig.useSASPlusEncoding = useSASPlusEncoding;
        LiftedTreePathConfig.useMacroAction = useMacroAction;
    }
}

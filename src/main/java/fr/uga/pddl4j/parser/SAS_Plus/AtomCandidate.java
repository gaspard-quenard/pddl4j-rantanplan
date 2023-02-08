package fr.uga.pddl4j.parser.SAS_Plus;

import java.util.Vector;

public class AtomCandidate {
    public String predSymbolName;
    public Vector<Integer> paramsId; // Index of the variable used of the parent Candidate for each parameter
    // public PddlCondAtom cond;
    public int isExactlyOne;
    public int isStatic;
    public Candidate candidateParent;

    public AtomCandidate(Candidate candidateParent, String predSymbolName) {
        this.candidateParent = candidateParent;
        this.predSymbolName = predSymbolName;
        this.paramsId = new Vector<Integer>();
    }

    // // Copy constructor
    public AtomCandidate(AtomCandidate source) {
        this.predSymbolName = source.predSymbolName;
        this.paramsId = new Vector<Integer>();
        for (Integer paramId : source.paramsId) {
            this.paramsId.add(paramId);
        }
        this.isExactlyOne = source.isExactlyOne;
        this.isStatic = source.isStatic;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(predSymbolName + " ");
        for (Integer paramId : this.paramsId) {
            sb.append(this.candidateParent.variables.get(paramId) + " ");
        }
        return sb.toString();
    }
}
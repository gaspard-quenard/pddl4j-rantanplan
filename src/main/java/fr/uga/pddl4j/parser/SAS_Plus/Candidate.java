package fr.uga.pddl4j.parser.SAS_Plus;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Vector;

public class Candidate {
    public int id; // ID of the candidate
    public Vector<AtomCandidate> mutexGroup;
    public Vector<AtomVariable> variables; // Set of variables which will be taken by the atoms of the candidate
    // public boolean eachPredOnlyOnce; /* !< True if each predicate is there only once */
    // public int refinedFrom; /* !< ID of the candidate this was refined from */
    // public boolean refinedVar; /* !< True if refined by changing variables */
    // public boolean refinedType; /* !< True if refined by changing types */
    // public boolean refinedByExtend; /* !< True if refined by adding predicates */
    // public int refinedByExtendPred;

    Candidate() {
        this.mutexGroup = new Vector<AtomCandidate>();
        this.variables = new Vector<>();
        // this.refinedFrom = -1;
        // this.refinedVar = false;
        // this.refinedType = false;
        // this.refinedByExtend = false;
        // this.eachPredOnlyOnce = true;
        // this.refinedByExtendPred = -1;
    }

    // Copy constructor
    public Candidate(Candidate source) {
        this.id = source.id;
        this.mutexGroup = new Vector<AtomCandidate>();
        for (AtomCandidate sourceAtomCandidate : source.mutexGroup) {
            AtomCandidate cpy = new AtomCandidate(sourceAtomCandidate);
            cpy.candidateParent = this;
            this.mutexGroup.add(cpy);
        }
        this.variables = new Vector<AtomVariable>();
        for (AtomVariable var : source.variables) {
            this.variables.add(new AtomVariable(var));
        }
        // this.eachPredOnlyOnce = source.eachPredOnlyOnce;
        // this.refinedFrom = source.refinedFrom;
        // this.refinedVar = source.refinedVar;
        // this.refinedType = source.refinedType;
        // this.refinedByExtend = source.refinedByExtend;
        // this.refinedByExtendPred = source.refinedByExtendPred;
    }

    /**
     * 
     * Determines if a given predicate is contained within the mutex group of
     * this candidate.
     * 
     * @param predicateName The name of the predicate to check for containment in
     *                      the mutex group
     * @return true if the predicate is contained within the mutex group, false
     *         otherwise
     */
    public boolean hasPredicateInMutexGroup(String predicateName) {
        for (AtomCandidate atomCandidate : mutexGroup) {
            if (atomCandidate.predSymbolName.equals(predicateName)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String toString() {
        return this.getUniqueStringRepresentation();
        // StringBuilder sb = new StringBuilder();
        // // sb.append("Candidate:" + "\n");
        // sb.append("{ ");
        // for (AtomCandidate pred : this.mutexGroup) {
        //     sb.append(pred);
        // }
        // sb.append("}\n");
        // return sb.toString();
    }

    /**
     * Generates a unique string representation of a candidate (two identical
     * candidate will always have the same string representation)
     *
     * @return a string representation of the candidate
     */
    public String getUniqueStringRepresentation() {
        StringBuilder candidateString = new StringBuilder();

        // Sort the array of mutexGroup by predSymbolName
        Collections.sort(this.mutexGroup, new Comparator<AtomCandidate>() {
            @Override
            public int compare(AtomCandidate a1, AtomCandidate a2) {
                return a1.predSymbolName.compareTo(a2.predSymbolName);
            }
        });

        // Variables that have already been seen
        List<Integer> seenVariables = new ArrayList<>();
        candidateString.append("{");
        for (int i = 0; i < this.mutexGroup.size(); i++) {
            AtomCandidate pred = this.mutexGroup.get(i);
            candidateString.append(pred.predSymbolName);
            for (Integer variableIdx : pred.paramsId) {
                AtomVariable variable = this.variables.get(variableIdx);
                if (variable.isCountedVar) {
                    candidateString.append(" C");
                } else {
                    candidateString.append(" V");
                }
                if (seenVariables.contains(variableIdx)) {
                    candidateString.append(seenVariables.indexOf(variableIdx));
                } else {
                    candidateString.append(seenVariables.size());
                    seenVariables.add(variableIdx);
                }
                candidateString.append(":" + variable.typeName);
            }
            if (i < this.mutexGroup.size() - 1) {
                candidateString.append(", ");
            }
        }
        candidateString.append("}");

        return candidateString.toString();
    }

}

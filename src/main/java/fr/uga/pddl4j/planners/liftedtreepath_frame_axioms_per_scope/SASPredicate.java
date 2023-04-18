package fr.uga.pddl4j.planners.liftedtreepath_frame_axioms_per_scope;

import java.util.ArrayList;

import fr.uga.pddl4j.parser.SAS_Plus.Candidate;

public class SASPredicate {

    // Thd id of the predicate
    int id;

    int lastDefined;

    String predicateName;

    String fullName;

    ArrayList<String> params;

    // A predicate can belong to multiples clique
    ArrayList<Clique> cliques;

    // The value of predicate into each of the cliques
    ArrayList<Integer> valueInCliques;

    public SASPredicate(int id, String predicateName, String fullName, ArrayList<String> paramsPredicates) {
        this.id = id;
        this.lastDefined = 0;
        this.predicateName = predicateName;
        this.fullName = fullName;
        this.cliques = new ArrayList<>();
        this.valueInCliques = new ArrayList<>();
        this.params = new ArrayList<>();
        this.params.addAll(paramsPredicates);
    }

    public void addClique(Clique clique, int value) {
        this.cliques.add(clique);
        this.valueInCliques.add(value);
    }   
    
    public int getLastTimePredicateWasDefined() {
        return this.lastDefined;
    }

    public void setLastTimePredicateWasDefined(int lastDefined) {
        this.lastDefined = lastDefined;
    }

    public String getFullName() {
        return this.fullName;
    }

    public ArrayList<String> getParams() {
        return this.params;
    }
}


class Clique {
    int idMutexGround;
    int nbBits;
    Candidate LFG;
    ArrayList<String> params;
    int numberValues;
    int id;
    int lastDefined = 0;
    static int idCounter = 0;

    public Clique(int idMutexGround, Candidate LFG, ArrayList<String> params) {
        this.idMutexGround = idMutexGround;
        this.LFG = LFG;
        this.params = params;
        this.numberValues = 1; // By default, the number of values is 1
        this.nbBits = 1;
        this.id = idCounter;
        Clique.idCounter++;
    }

    public void setNumberValues(int numberValues) {
        this.numberValues = numberValues;
        this.nbBits = (int) Math.ceil((Math.log(numberValues) / Math.log(2)));
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("Clique " + this.id + " Mutex group: " + LFG.toString() + " params: ");
        for (String param : this.params) {
            sb.append(param);
        }
        return sb.toString();
    }

    public int getNbBits() {
        return nbBits;
    }

    public int getLastTimeCliqueWasDefined() {
        return this.lastDefined;
    }

    public void setLastTimeCliqueWasDefined(int lastDefined) {
        this.lastDefined = lastDefined;
    }
}

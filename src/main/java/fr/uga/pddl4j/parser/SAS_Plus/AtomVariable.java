package fr.uga.pddl4j.parser.SAS_Plus;

public class AtomVariable {

    public static int nbAtomVariable;

    public int id;
    public boolean isCountedVar;
    public int inherit;
    public String typeName;
    public String value; // Get a specific value when we unify a Candidate

    AtomVariable(String typeName, boolean isCountedVar) {
        AtomVariable.nbAtomVariable++;
        this.id = AtomVariable.nbAtomVariable;
        this.typeName = typeName;
        this.inherit = -1;
        this.isCountedVar = isCountedVar;
        this.value = null;
    }

    // Copy constructor
    AtomVariable(AtomVariable source) {
        AtomVariable.nbAtomVariable++;
        this.id = AtomVariable.nbAtomVariable;
        this.isCountedVar = source.isCountedVar;
        this.inherit = source.inherit;
        this.typeName = source.typeName;
        this.value = source.value;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (this.isCountedVar) {

            sb.append("C");
        } else {
            sb.append("V");
        }
        sb.append(this.id + ":" + this.typeName);
        return sb.toString();
    }
}

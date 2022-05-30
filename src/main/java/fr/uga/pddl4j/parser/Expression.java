package fr.uga.pddl4j.parser;

import fr.uga.pddl4j.parser.lexer.Token;
import fr.uga.pddl4j.problem.AtomicFormulaSimplifier;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

public class Expression<T> implements Locatable, Iterable<Expression<T>>, Serializable {

    /**
     * The type of the node.
     */
    private PDDLConnective connective;

    /**
     * The symbol used in the atomic formula. The symbol can be a function symbol a predicate symbol or a task symbol.
     */
    private Symbol<T> symbol;

    /**
     * The arguments of the atomic formula of this expression.
     */
    private List<Symbol<T>> arguments;

    /**
     * only for parsing: the variable in quantifiers.
     */
    private List<TypedSymbol<T>> quantifiedVariables;

    /**
     * The value associate to this expression.
     */
    private Double value;

    /**
     * The children expression of this expression.
     */
    private List<Expression<T>> children;

    /**
     * The name of the preference.
     */
    private Symbol<T> prefName;

    /**
     * The variable.
     */
    private Symbol<T> variable;

    /**
     * The taskID. Use to the alias of a task atom.
     */
    private Symbol<T> taskID;

    /**
     * A flag to indicate if this expression represents a primitive task.
     */
    private boolean isPrimtive;

    /**
     * The time specifier of the symbol.
     */
    private TimeSpecifier timeSpecifier;

    /**
     * The location of the expression.
     */
    private Location location;

    /**
     * Creates a new expression from another.
     *
     * @param other the other expression.
     */
    public Expression(final Expression<T> other) {
        super();
        this.setConnective(other.getConnective());
        if (other.getSymbol() != null) {
            this.setSymbol(new Symbol<>(other.getSymbol()));
        }
        if (other.getArguments() != null) {
            this.setArguments(new ArrayList<>());
            this.getArguments().addAll(other.getArguments().stream()
                .map(Symbol<T>::new).collect(Collectors.toList()));
        }
        if (other.getQuantifiedVariables() != null) {
            this.setQuantifiedVariables(new ArrayList<>());
            this.getQuantifiedVariables().addAll(other.getQuantifiedVariables().stream()
                .map(TypedSymbol<T>::new).collect(Collectors.toList()));
        }
        if (other.getVariable() != null) {
            this.setVariable(new Symbol<>(other.getVariable()));
        }
        if (other.getPrefName() != null) {
            this.setPrefName(new Symbol<>(other.getPrefName()));
        }
        if (other.getTaskID() != null) {
            this.setTaskID(new Symbol<>(other.getTaskID()));
        }
        if (other.getValue() != null) {
            this.setValue(other.getValue());
        }
        if (other.getChildren() != null) {
            this.setChildren(new ArrayList<>());
            this.getChildren().addAll(other.getChildren().stream()
                .map(Expression<T>::new).collect(Collectors.toList()));
        }
        this.setPrimtive(other.isPrimtive());
        if (other.getLocation() != null) {
            this.setLocation(new Location(other.getLocation()));
        }
        this.setTimeSpecifier(other.getTimeSpecifier());
    }

    /**
     * Creates a new expression with a specified connective.
     *
     * @param connective the connective.
     */
    public Expression(final PDDLConnective connective) {
        super();
        this.setConnective(connective);
        this.setSymbol(null);
        this.setArguments(new ArrayList<>());
        this.setQuantifiedVariables(new ArrayList<>());
        this.setValue(null);
        this.setVariable(null);
        this.setChildren(new ArrayList<>());
        this.setPrefName(null);
        this.setTaskID(null);
        this.setPrimtive(false);
        this.setTimeSpecifier(null);
        this.setLocation(null);
    }

    /**
     * Creates a new empty AND expression.
     */
    public Expression() {
        this(PDDLConnective.AND);
    }

    /**
     * Returns the connective of this expression.
     *
     * @return the connective of this expression.
     */
    public final PDDLConnective getConnective() {
        return this.connective;
    }

    /**
     * Set the connective of this expression.
     *
     * @param connective the connective.
     */
    public final void setConnective(final PDDLConnective connective) {
        this.connective = connective;
    }

    /**
     * Returns the symbol to this expression. Expression with a symbol are predicate, function or task formula.
     *
     * @return the symbol the new symbol of this expression. If this expression is not ATOM, a FUNCTION or TASK the
     * returned symbol is null.
     */
    public final Symbol<T> getSymbol() {
        return this.symbol;
    }

    /**
     * Sets a new symbol to this expression. Expression with a symbol are predicate, function or task formula.
     *
     * @param symbol the new symbol of this expression.
     */
    public final void setSymbol(final Symbol<T> symbol) {
        this.symbol = symbol;
    }

    /**
     * Returns the arguments of the atomic formula represented by this expression.
     *
     * @return the arguments of the atomic formula represented by this expression.
     */
    public final List<Symbol<T>> getArguments() {
        return this.arguments;
    }

    /**
     * Sets the argument of the atomic formula represented by this expression.
     *
     * @param arguments the arguments of the atomic formula represented by this expression.
     */
    public final void setArguments(final List<Symbol<T>> arguments) {
        this.arguments = arguments;
    }

    /**
     * Adds an argument to this expression.
     *
     * @param argument the argument to add.
     */
    public final boolean addArgument(final Symbol<T> argument) {
        if (this.getArguments() == null) {
            this.setArguments(new ArrayList<>());
        }
        return this.arguments.add(argument);
    }


    /**
     * Returns the list of quantified variables of this expression.
     *
     * @return the list of quantified variables of this expression.
     */
    public final List<TypedSymbol<T>> getQuantifiedVariables() {
        return this.quantifiedVariables;
    }

    /**
     * Sets the quantified variables of this expression.
     *
     * @param variables the quantified variables of this expression.
     */
    public final void setQuantifiedVariables(final List<TypedSymbol<T>> variables) {
        this.quantifiedVariables = variables;
    }

    /**
     * Adds a quantified variable to this expression.
     *
     * @param variable the quantified variable to add.
     */
    public final boolean addQuantifiedVariable(final TypedSymbol<T> variable) {
        if (this.getQuantifiedVariables() == null) {
            this.setQuantifiedVariables(new ArrayList<>());
        }
        return this.quantifiedVariables.add(variable);
    }

    /**
     * Returns the numeric value of this parser node.
     *
     * @return the numeric value of this parser node.
     */
    public final Double getValue() {
        return this.value;
    }

    /**
     * Set the numeric value of this expression.
     *
     * @param value the numeric value of this expression.
     */
    public final void setValue(final Double value) {
        this.value = value;
    }

    /**
     * Returns the variable of this expression
     *
     * @return the variable of this expression.
     */
    public final Symbol<T> getVariable() {
        return this.symbol;
    }

    /**
     * Sets a new variable to this parser node.
     *
     * @param variable the new variable to set.
     */
    public final void setVariable(final Symbol<T> variable) {
        this.variable = variable;
    }

    /**
     * Returns the name of the preference associated to this expression.
     *
     * @return the name of the preference or <code>null</code> if the preference name was not initialized.
     */
    public final Symbol<T> getPrefName() {
        return this.prefName;
    }

    /**
     * Sets a name to the preference associated to this expression.
     *
     * @param name the name of the preference to set.
     */
    public final void setPrefName(final Symbol<T> name) {
        this.prefName = name;
    }

    /**
     * Returns the taskID associated to this expression. The taskID is only use in HTN planning to make alias of task.
     *
     * @return the taskID associated to this expression.
     */
    public final Symbol<T> getTaskID() {
        return this.taskID;
    }

    /**
     * Set the taskID associated to this expression. The taskID is only use in HTN planning to make alias of task.
     *
     * @param taskID the taskID to set.
     */
    public final void setTaskID(Symbol<T> taskID) {
        this.taskID = taskID;
    }

    /**
     * Add a new child expression to this expression.
     *
     * @param exp the child to add
     * @return <code>true</code> if the expression was added; <code>false</code> otherwise
     * @throws RuntimeException if the specified node is null
     */
    public final boolean addChild(final Expression<T> exp) {
        if (this.getChildren() == null) {
            this.setChildren(new ArrayList<>());
        }
        return this.children.add(exp);
    }

    /**
     * Sets the list of children expressions of this expression.
     *
     * @param children the children expression to set.
     */
    public final void setChildren(final List<Expression<T>> children) {
        this.children = children;
    }

    /**
     * Returns the list of children of this expression.
     *
     * @return the list of children of this expression.
     */
    public final List<Expression<T>> getChildren() {
        return this.children;
    }

    /**
     * Returns <code>true</code> if the expression is a primitive task.
     *
     * @return <code>true</code> if the expression is a primitive task, <code>false</code> otherwise.
     */
    public final boolean isPrimtive() {
        return this.isPrimtive;
    }

    /**
     * Sets the boolean flag used to specified if the expression is a primitive task to a specified value.
     *
     * @param flag the flag.
     */
    public final void setPrimtive(final boolean flag) {
        this.isPrimtive = flag;
    }

    /**
     * Returns the time specifier of the symbol.
     *
     * @return the time specifier of the symbol.
     */
    public final TimeSpecifier getTimeSpecifier() {
        return this.timeSpecifier;
    }

    /**
     * Sets the time specifier of the symbol.
     *
     * @param  timeSpecifier the time specifier to set.
     */
    public final void setTimeSpecifier(final TimeSpecifier timeSpecifier) {
        this.timeSpecifier = timeSpecifier;
    }


    /**
     * Return the location of the symbol.
     *
     * @return the location of the symbol.
     */
    public final Location getLocation() {
        return this.location;
    }

    /**
     * Sets the location of the symbol.
     *
     * @param location the location to set.
     */
    public final void setLocation(Location location) {
        this.location = location;
    }

    /**
     * Sets the begin line and column of the expression from a specified token.
     *
     * @param begin the first token of the expression.
     */
    public final void setBegin(final Token begin) {
        if (this.getLocation() == null) {
            this.setLocation(new Location());
        }
        this.getLocation().setBegin(begin);
    }

    /**
     * Sets the end line and column of the expression from a specified token.
     *
     * @param end the last token of the expression.
     */
    public final void setEnd(final Token end) {
        if (this.getLocation() == null) {
            this.setLocation(new Location());
        }
        this.getLocation().setEnd(end);
    }

    /**
     * Assigns a specified expression to this expression. After the method call the expression is equals to the
     * expression in parameter. The assignment is swallow, i.e., the assignment does not make a deep copy of the content
     * of the expression in parameter.
     *
     * @param exp the expression to assigned to this expression.
     */
    public final void assign(Expression<T> exp) {
        this.setConnective(exp.getConnective());
        this.setSymbol(exp.getSymbol());
        this.setArguments(exp.getArguments());
        this.setQuantifiedVariables(exp.getQuantifiedVariables());
        this.setValue(exp.getValue());
        this.setVariable(exp.getVariable());
        this.setChildren(exp.getChildren());
        this.setPrefName(exp.getPrefName());
        this.setTaskID(exp.getTaskID());
        this.setPrimtive(exp.isPrimtive());
        this.setLocation(exp.getLocation());
    }

    /**
     * Returns if this expression is a literal. A literal is an atomic formula or a negated atomic
     * formula.
     *
     * @return <code>true</code> if this expression is a literal <code>false</code> otherwise.
     */
    public final boolean isLiteral() {
        return this.getConnective().equals(PDDLConnective.ATOM)
            || (this.getConnective().equals(PDDLConnective.NOT)
            && this.getChildren().size() == 1
            && this.getChildren().get(0).getConnective().equals(PDDLConnective.ATOM));
    }

    /**
     * Sets the expression into negative normal form. After the method call, negation can occurs only before atomic
     * formula and time specifier (at start, at end, overall) can only occur before literal. The method is applicable on
     * expressions containing a goal description, i.e., NOT, AND, OR, WHEN, IMPLY, SOMETIME_AFTER, SOMETIME_BEFORE,
     * FORALL, EXISTS, ALWAYS, AT_MOST_ONCE, WITHIN, HOLD_AFTER, ALWAYS_WITHIN, HOLD_DURING, AT_START, AT_END, OVERALL,
     * ATOM, EQUAL_ATOM, EQUAL, LESS, LESS_OR_EQUAL, GREATER, GREATER_OR_EQUAL, ASSIGN, INCREASE, DECREASE, SCALE_UP,
     * SCALE_DOWN, TRUE and FALSE.
     *
     * @throws MalformedExpressionException if this expression is malformed.
     */
    public final void toNNF()  {

        switch (this.getConnective()) {
            case NOT:
                this.moveNegationInward();
                break;
            case AND:
            case OR:
            case WHEN:
            case IMPLY:
            case SOMETIME_AFTER_CONSTRAINT:
            case SOMETIME_BEFORE_CONSTRAINT:
            case FORALL:
            case EXISTS:
            case AT_END_CONSTRAINT:
            case ALWAYS_CONSTRAINT:
            case AT_MOST_ONCE_CONSTRAINT:
            case HOLD_AFTER_METHOD_CONSTRAINT:
            case HOLD_BEFORE_METHOD_CONSTRAINT:
            case AT_END_METHOD_CONSTRAINT:
            case AT_START_METHOD_CONSTRAINT:
            case ALWAYS_METHOD_CONSTRAINT:
            case AT_MOST_ONCE_METHOD_CONSTRAINT:
            case SOMETIME_METHOD_CONSTRAINT:
            case SOMETIME_BEFORE_METHOD_CONSTRAINT:
            case SOMETIME_AFTER_METHOD_CONSTRAINT:
            case HOLD_BETWEEN_METHOD_CONSTRAINT:
            case HOLD_DURING_METHOD_CONSTRAINT:
            case WITHIN_CONSTRAINT:
            case HOLD_AFTER_CONSTRAINT:
            case ALWAYS_WITHIN_CONSTRAINT:
            case HOLD_DURING_CONSTRAINT:
                this.getChildren().forEach(Expression::toNNF);
                break;
            case AT_START:
            case AT_END:
            case OVER_ALL:
                this.moveTimeSpecifierInward();
                break;
            case ATOM:
            case EQUAL_ATOM:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case ASSIGN:
            case INCREASE:
            case DECREASE:
            case SCALE_UP:
            case SCALE_DOWN:
            case TASK_ID:
            case NUMBER:
            case TRUE:
            case FALSE:
                // Do nothing
                break;
            default:
                throw new UnexpectedExpressionException(this.toString());
        }
    }

    /**
     * Moves the negation inward the expression.
     *
     * @throws UnexpectedExpressionException if the expression is not composed of expressions that are not FORALL,
     *      EXISTS, AND, OR, NOT, GREATER, LESS, GREATER_OR_EQUAL, LESS_OR_EQUAL, EQUAL, ATOM or EQUAL_ATOM.
     */
    public final void moveNegationInward() {
        assert this.getConnective().equals(PDDLConnective.NOT);

        final Expression<T> child = this.getChildren().get(0);
        switch (child.getConnective()) {
            case FORALL:
                this.setConnective(PDDLConnective.EXISTS);
                this.setQuantifiedVariables(child.getQuantifiedVariables());
                Expression<T> negation = new Expression<>(PDDLConnective.NOT);
                negation.addChild(child.getChildren().get(0));
                negation.toNNF();
                this.getChildren().set(0, negation);
                break;
            case EXISTS:
                this.setConnective(PDDLConnective.FORALL);
                this.setQuantifiedVariables(child.getQuantifiedVariables());
                negation = new Expression<>(PDDLConnective.NOT);
                negation.addChild(child.getChildren().get(0));
                negation.toNNF();
                this.getChildren().set(0, negation);
                break;
            case AND:
                this.setConnective(PDDLConnective.OR);
                this.getChildren().clear();
                for (int i = 0; i < child.getChildren().size(); i++) {
                    negation = new Expression<>(PDDLConnective.NOT);
                    negation.addChild(child.getChildren().get(i));
                    negation.toNNF();
                    this.getChildren().add(negation);
                }
                break;
            case OR:
                this.setConnective(PDDLConnective.AND);
                this.getChildren().clear();
                for (int i = 0; i < child.getChildren().size(); i++) {
                    negation = new Expression<>(PDDLConnective.NOT);
                    negation.addChild(child.getChildren().get(i));
                    negation.toNNF();
                    this.getChildren().add(negation);
                }
                break;
            case NOT:
                this.assign(child.getChildren().get(0));
                this.toNNF();
                break;
            case IMPLY: // (not (imply p q)) -> (imply (not p) (not q))
                this.setConnective(PDDLConnective.IMPLY);
                final Expression notp = new Expression<>(PDDLConnective.NOT);
                notp.addChild(child.getChildren().get(0));
                notp.toNNF();
                final Expression notq = new Expression<>(PDDLConnective.NOT);
                notq.addChild(child.getChildren().get(1));
                notq.toNNF();
                this.getChildren().clear();
                this.getChildren().add(notp);
                this.getChildren().add(notq);
                break;
            case AT_START:
            case AT_END:
            case OVER_ALL:
                this.setConnective(child.getConnective());
                child.setConnective(PDDLConnective.NOT);
                break;
            case TRUE:
                this.setConnective(PDDLConnective.FALSE);
                break;
            case FALSE:
                this.setConnective(PDDLConnective.TRUE);
                break;
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case ATOM:
            case EQUAL_ATOM:
                // Do nothing
                break;

            default:
                throw new UnexpectedExpressionException(this.toString());
        }
    }

    /**
     * Move the time specifier inward the expression.
     *
     * @throws UnexpectedExpressionException if the expression is not composed of expressions that are not FORALL,
     *      EXISTS, AND, OR, NOT, GREATER, LESS, GREATER_OR_EQUAL, LESS_OR_EQUAL, EQUAL, ATOM or EQUAL_ATOM.
     */
    public final void moveTimeSpecifierInward() {
        assert this.getConnective().equals(PDDLConnective.AT_START)
            || this.getConnective().equals(PDDLConnective.AT_END)
            || this.getConnective().equals(PDDLConnective.OVER_ALL);

        final Expression<T> child = this.getChildren().get(0);
        switch (child.getConnective()) {
            case FORALL:
            case EXISTS:
                Expression timeExp = new Expression<>(this.getConnective());
                timeExp.addChild(child.getChildren().get(0));
                timeExp.moveTimeSpecifierInward();
                this.getChildren().set(0, timeExp);
                this.setConnective(child.getConnective());
                this.setQuantifiedVariables(child.getQuantifiedVariables());
                break;
            case AND:
            case OR:
                this.getChildren().clear();
                for (int i = 0; i < child.getChildren().size(); i++) {
                    timeExp = new Expression<>(this.getConnective());
                    timeExp.addChild(child.getChildren().get(i));
                    timeExp.moveTimeSpecifierInward();
                    this.getChildren().add(timeExp);
                }
                this.setConnective(child.getConnective());
                break;
            case NOT:
                child.toNNF();
                if (!child.getConnective().equals(PDDLConnective.NOT)) {
                    this.moveTimeSpecifierInward();
                }
                break;
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case ATOM:
            case EQUAL_ATOM:
                // Do nothing
                break;
            default:
                throw new UnexpectedExpressionException(this.toString());
        }
    }

    /**
     * Expands the quantified expressions contained in a specified expression.
     *
     */
    /*public void expandQuantifiedExpression(Map<T, Set<Symbol<T>>> domains) {
        this.expandQuantifiedExpression(domains, null);
    }
    /**
     * Expands the quantified expressions contained in a specified expression.
     *
     */
    public void expandQuantifiedExpression(Map<T, Set<Symbol<T>>> domains, AtomicFormulaSimplifier<T> simplifier) {
        switch (this.getConnective()) {
            case AND:
                Iterator<Expression<T>> i = this.getChildren().iterator();
                while (i.hasNext() && this.getConnective().equals(PDDLConnective.AND)) {
                    final Expression<T> ei = i.next();
                    // Remove quantified expression where the domain of the quantified variable is empty
                    if ((ei.getConnective().equals(PDDLConnective.FORALL)
                        || ei.getConnective().equals(PDDLConnective.EXISTS))
                        && domains.get(ei.getQuantifiedVariables().get(0).getTypes().get(0).getValue()).isEmpty()) {
                        i.remove();
                    } else {
                        ei.expandQuantifiedExpression(domains, simplifier);
                        // If a child expression is FALSE, the whole conjunction becomes FALSE.
                        if (ei.getConnective().equals(PDDLConnective.FALSE)) {
                            this.setConnective(PDDLConnective.FALSE);
                        }
                    }
                }
                break;
            case OR:
                i = this.getChildren().iterator();
                while (i.hasNext() && this.getConnective().equals(PDDLConnective.OR)) {
                    final Expression<T> ei = i.next();
                    // Remove quantified expression where the domain of the quantified variable is empty
                    if ((ei.getConnective().equals(PDDLConnective.FORALL)
                        || ei.getConnective().equals(PDDLConnective.EXISTS))
                        && domains.get(ei.getQuantifiedVariables().get(0).getTypes().get(0).getValue()).isEmpty()) {
                        i.remove();
                        continue;
                    }
                    ei.expandQuantifiedExpression(domains, simplifier);
                    // If a child expression is TRUE, the whole disjunction becomes TRUE.
                    if (ei.getConnective().equals(PDDLConnective.TRUE)) {
                        this.setConnective(PDDLConnective.TRUE);
                    }
                }
                break;
            case FORALL:
                Set<Symbol<T>> constants = domains.get(this.getQuantifiedVariables().get(0).getTypes().get(0).getValue());
                Expression<T> qExp = this.getChildren().get(0);
                Symbol<T> var = this.getQuantifiedVariables().get(0);
                this.setConnective(PDDLConnective.AND);
                this.getChildren().clear();
                Iterator<Symbol<T>> it = constants.iterator();
                while (it.hasNext() && this.getConnective().equals(PDDLConnective.AND)) {
                    Symbol<T> cons = it.next();
                    Expression<T> copy = new Expression<>(qExp);
                    copy.substitute(var, cons, simplifier);
                    this.getChildren().add(copy);
                    // If a child expression is FALSE, the whole conjunction becomes FALSE.
                    if (copy.getConnective().equals(PDDLConnective.FALSE)) {
                        this.setConnective(PDDLConnective.FALSE);
                    }
                }
                this.expandQuantifiedExpression(domains, simplifier);
                break;
            case EXISTS:
                constants = domains.get(this.getQuantifiedVariables().get(0).getTypes().get(0).getValue());
                qExp = this.getChildren().get(0);
                var = this.getQuantifiedVariables().get(0);
                this.setConnective(PDDLConnective.OR);
                this.getChildren().clear();
                it = constants.iterator();
                while (it.hasNext() && this.getConnective().equals(PDDLConnective.OR)) {
                    Symbol<T> cons = it.next();
                    Expression<T> copy = new Expression<>(qExp);
                    copy.substitute(var, cons, simplifier);
                    this.getChildren().add(copy);
                    // If a child expression is TRUE, the whole disjunction becomes TRUE.
                    if (copy.getConnective().equals(PDDLConnective.TRUE)) {
                        this.setConnective(PDDLConnective.TRUE);
                    }
                }
                this.expandQuantifiedExpression(domains, simplifier);
                break;
            case AT_START:
            case AT_END:
            case NOT:
            case ALWAYS_CONSTRAINT:
            case OVER_ALL:
            case SOMETIME_CONSTRAINT:
            case AT_MOST_ONCE_CONSTRAINT:
                this.getChildren().get(0).expandQuantifiedExpression(domains, simplifier);
                break;
            case SOMETIME_AFTER_CONSTRAINT:
            case SOMETIME_BEFORE_CONSTRAINT:
            case WITHIN_CONSTRAINT:
            case HOLD_AFTER_CONSTRAINT:
            case WHEN:
                this.getChildren().get(0).expandQuantifiedExpression(domains, simplifier);
                this.getChildren().get(1).expandQuantifiedExpression(domains, simplifier);
                break;
            case ALWAYS_WITHIN_CONSTRAINT:
            case HOLD_DURING_CONSTRAINT:
                this.getChildren().get(0).expandQuantifiedExpression(domains, simplifier);
                this.getChildren().get(1).expandQuantifiedExpression(domains, simplifier);
                this.getChildren().get(2).expandQuantifiedExpression(domains, simplifier);
                break;
            case ATOM:
                if (simplifier != null) {
                    simplifier.simplify(this);
                }
                break;
            case EQUAL_ATOM:
            case FN_HEAD:
            case FN_ATOM:
            case TIMED_LITERAL:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case ASSIGN:
            case INCREASE:
            case DECREASE:
            case SCALE_UP:
            case SCALE_DOWN:
            case MULTIPLICATION:
            case DIVISION:
            case MINUS:
            case PLUS:
            case F_EXP_T:
            case NUMBER:
            case MINIMIZE:
            case MAXIMIZE:
            case UMINUS:
            case F_EXP:
            case TIME_VAR:
            case IS_VIOLATED:
                // do nothing
                break;
            default:
                // do nothing
        }
    }

    /**
     * Substitutes all occurrence of a specified variable into an expression by a constant.
     *
     * @param var  the variable.
     * @param cons the constant.
     */
    public boolean substitute(final Symbol<T> var, final  Symbol<T> cons) {
        return this.substitute(var, cons, null);
    }

    /**
     * Substitutes all occurrence of a specified variable into an expression by a constant.
     *
     * @param var  the variable.
     * @param cons the constant.
     */
    public boolean substitute(final Symbol<T> var, final  Symbol<T> cons, final AtomicFormulaSimplifier simplifier) {

        boolean updated = false;
        switch (this.getConnective()) {
            case ATOM:
                List<Symbol<T>> arguments = this.getArguments();
                for (int i = 0; i < arguments.size(); i++) {
                    if (arguments.get(i).equals(var)) {
                        arguments.set(i, cons);
                        updated = true;
                    }
                }
                if (updated) {
                    simplifier.simplify(this);
                }
                break;
            case TASK:
                arguments = this.getArguments();
                for (int i = 0; i < arguments.size(); i++) {
                    if (arguments.get(i).equals(var)) {
                        arguments.set(i, cons);
                        updated = true;
                    }
                }
                break;
            case FN_HEAD:
                arguments = this.getArguments();
                for (int i = 0; i < arguments.size(); i++) {
                    if (arguments.get(i).equals(var)) {
                        arguments.set(i, cons);
                        updated = true;
                    }
                }
                //if (updated) {
                //    Instantiation.simplyFunction(exp);
                //}
                break;
            case EQUAL_ATOM:
                arguments = this.getArguments();
                // Get and substitute the first argument
                final Symbol<T> arg1 = arguments.get(0);
                if (arg1.equals(var)) {
                    arguments.set(0, cons);
                    updated = true;
                }
                // Get and substitute the second argument
                final Symbol<T> arg2 = arguments.get(1);
                if (arg2.equals(var)) {
                    arguments.set(1, cons);
                    updated = true;
                }
                // The equality is TRUE: arg1 and arg2 are the same variable or the same constant
                if (arg1.equals(arg2)) {
                    this.setConnective(PDDLConnective.TRUE);
                } else if (arg1.getType().equals(SymbolType.CONSTANT)
                    && arg2.getType().equals(SymbolType.CONSTANT)
                    && arg1.getValue().equals(arg2.getValue())) {
                    // The equality is ground and the equality is FALSE because arg1 != arg2
                    this.setConnective(PDDLConnective.FALSE);
                }
                break;
            case AND:
                Iterator<Expression<T>> i = this.getChildren().iterator();
                while (i.hasNext() && this.getConnective().equals(PDDLConnective.AND)) {
                    final Expression<T> ei = i.next();
                    updated |= ei.substitute(var, cons, simplifier);
                    // If a child expression is FALSE, the whole conjunction becomes FALSE.
                    if (ei.getConnective().equals(PDDLConnective.FALSE)) {
                        this.setConnective(PDDLConnective.FALSE);
                    }
                }
                break;
            case OR:
                i = this.getChildren().iterator();
                while (i.hasNext() && this.getConnective().equals(PDDLConnective.OR)) {
                    final Expression<T> ei = i.next();
                    updated |= ei.substitute(var, cons, simplifier);
                    // If a child expression is TRUE, the whole disjunction is TRUE.
                    if (ei.getConnective().equals(PDDLConnective.TRUE)) {
                        this.setConnective(PDDLConnective.TRUE);
                    }
                }
                break;
            case NOT:
                final Expression<T> neg = this.getChildren().get(0);
                neg.substitute(var, cons, simplifier);
                if (neg.getConnective().equals(PDDLConnective.TRUE)) {
                    this.setConnective(PDDLConnective.FALSE);
                } else if (neg.getConnective().equals(PDDLConnective.FALSE)) {
                    this.setConnective(PDDLConnective.TRUE);
                }
                break;
            case WHEN:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case ASSIGN:
            case INCREASE:
            case DECREASE:
            case SCALE_UP:
            case SCALE_DOWN:
            case MULTIPLICATION:
            case DIVISION:
            case MINUS:
            case PLUS:
            case SOMETIME_AFTER_CONSTRAINT:
            case SOMETIME_BEFORE_CONSTRAINT:
            case WITHIN_CONSTRAINT:
            case HOLD_AFTER_CONSTRAINT:
                updated |= this.getChildren().get(0).substitute(var, cons, simplifier);
                updated |= this.getChildren().get(1).substitute(var, cons, simplifier);
                break;
            case FORALL:
            case EXISTS:
            case AT_START:
            case AT_END:
            case UMINUS:
            case ALWAYS_CONSTRAINT:
            case OVER_ALL:
            case SOMETIME_CONSTRAINT:
            case AT_MOST_ONCE_CONSTRAINT:
            case F_EXP:
                updated |= this.getChildren().get(0).substitute(var, cons, simplifier);
                break;
            case F_EXP_T:
                if (!this.getChildren().isEmpty()) {
                    updated |= this.getChildren().get(0).substitute(var, cons, simplifier);
                }
                break;
            case ALWAYS_WITHIN_CONSTRAINT:
            case HOLD_DURING_CONSTRAINT:
                updated |= this.getChildren().get(0).substitute(var, cons, simplifier);
                updated |= this.getChildren().get(1).substitute(var, cons, simplifier);
                updated |= this.getChildren().get(2).substitute(var, cons, simplifier);
                break;
            case FN_ATOM:
            case NUMBER:
            case TIMED_LITERAL:
            case TIME_VAR:
            case IS_VIOLATED:
            case MINIMIZE:
            case MAXIMIZE:
                break;
            default:
                // do nothing
        }
        return updated;
    }

    /**
     * This method simplify a specified expression. The rules of simplification are as below:
     * <ul></ul>
     * <li> not true eqv false </li>
     * <li> true ^ phi eqv phi </li>
     * <li> false ^ phi eqv false </li>
     * <li> true v phi eqv true </li>
     * <li> false v phi eqv false </li>
     * <li> not false eqv true </li>
     * <li> phi ^ phi eqv phi </li>
     * <li> phi v phi eqv phi </li>
     * <li> phi ^ not phi eqv false </li>
     * <li> phi v not phi eqv true </li>
     * <li> x = x eqv true </li>
     * <li> x = y eqv false </li>
     * </ul>
     *
     * @return <code>true</code> if the expression was simplified; <code>false</code> otherwise.
     * @throws UnexpectedExpressionException if the expression is not composed of expressions that are not FORALL,
     *      EXISTS, AND, OR, NOT, GREATER, LESS, GREATER_OR_EQUAL, LESS_OR_EQUAL, EQUAL, ATOM or EQUAL_ATOM, WHEN, TRUE,
     *      FALSE, HOLD_AFTER_METHOD_CONSTRAINT, HOLD_BEFORE_METHOD_CONSTRAINT, AT_END_METHOD_CONSTRAINT,
     *      AT_START_METHOD_CONSTRAINT, ALWAYS_METHOD_CONSTRAINT, AT_MOST_ONCE_METHOD_CONSTRAINT,
     *      SOMETIME_METHOD_CONSTRAINT, SOMETIME_BEFORE_METHOD_CONSTRAINT, SOMETIME_AFTER_METHOD_CONSTRAINT,
     *      HOLD_BETWEEN_METHOD_CONSTRAINT, HOLD_DURING_METHOD_CONSTRAINT.
     */
    public final boolean simplify() {
        boolean simplified = false;
        switch (this.getConnective()) {
            case EQUAL_ATOM:
                List<Symbol<T>> args = this.getArguments();
                // Get and substitute the first argument
                final Symbol<T> arg1 = args.get(0);
                // Get and substitute the second argument
                final Symbol<T> arg2 = args.get(1);
                // The equality is TRUE: arg1 and arg2 are the same variable or the same constant
                if (arg1.equals(arg2)) {
                    this.setConnective(PDDLConnective.TRUE);
                    simplified = true;
                } else if (arg1.getType().equals(SymbolType.CONSTANT)
                        && arg2.getType().equals(SymbolType.CONSTANT)
                        && !arg1.getValue().equals(arg2.getValue())) {
                    // The equality is ground and the equality is FALSE because arg1 != arg2
                    this.setConnective(PDDLConnective.FALSE);
                    simplified = true;
                }
                break;
            case AND:
                int i = 0;
                while (i < this.getChildren().size() && this.getConnective().equals(PDDLConnective.AND)) {
                    final Expression<T> ei = this.getChildren().get(i);
                    simplified &= ei.simplify();
                    if (ei.getConnective().equals(PDDLConnective.FALSE)) {
                        // If a child expression is FALSE, the whole conjunction becomes FALSE.
                        this.setConnective(PDDLConnective.FALSE);
                        simplified = true;
                    } else if (ei.getConnective().equals(PDDLConnective.TRUE)) {
                        // If a child expression is TRUE, we can remove the child expression.
                        this.getChildren().remove(i);
                        simplified = true;
                    } else if (ei.getConnective().equals(PDDLConnective.AND)) {
                        // If the child expression to add is a conjunction, we can simplify the expression by
                        this.getChildren().remove(i); // removing the inner conjunction.
                        simplified = true;
                        int j = 0;
                        int added = 0;
                        while (j < ei.getChildren().size() && this.getConnective().equals(PDDLConnective.AND)) {
                            final Expression<T> ej = ei.getChildren().get(j);
                            if (ej.getConnective().equals(PDDLConnective.FALSE)) {
                                this.setConnective(PDDLConnective.FALSE);
                            } else if (!ej.getConnective().equals(PDDLConnective.TRUE)) {
                                this.getChildren().add(i + added, ej);
                                added++;
                            }
                            j++;
                        }
                        i += added + 1;
                    } else if (ei.getConnective().equals(PDDLConnective.WHEN)) {
                        // Simplification of the conditional expression.
                        final Expression<T> antecedent = ei.getChildren().get(0);
                        final Expression<T> consequent = ei.getChildren().get(1);
                        // If the antecedent of a conditional effect becomes FALSE , the conditional
                        // effect is removed from the action. In this case, the effect is never applicable
                        // because it requires FALSE to hold, i.e., the state must be inconsistent.
                        if (antecedent.getConnective().equals(PDDLConnective.FALSE)) {
                            this.getChildren().remove(i);
                            simplified = true;
                        } else if (antecedent.getConnective().equals(PDDLConnective.TRUE)) {
                            // If the antecedent of a conditional effect becomes TRUE, the conditional
                            // effect becomes unconditional.
                            if (consequent.getConnective().equals(PDDLConnective.AND)) {
                                this.getChildren().remove(i);
                                int j = 0;
                                int added = 0;
                                while (j < consequent.getChildren().size()
                                    && this.getConnective().equals(PDDLConnective.AND)) {
                                    final Expression<T> ej = consequent.getChildren().get(j);
                                    if (ej.getConnective().equals(PDDLConnective.FALSE)) {
                                        this.setConnective(PDDLConnective.FALSE);
                                    } else if (!ej.getConnective().equals(PDDLConnective.TRUE)) {
                                        this.getChildren().add(i + added, ej);
                                        added++;
                                    }
                                    j++;
                                    simplified = true;
                                }
                                i += added + 1;
                            } else {
                                this.getChildren().set(i, consequent);
                                i++;
                                simplified = true;
                            }
                        } else if (consequent.getConnective().equals(PDDLConnective.TRUE)) {
                            // If the consequent of a conditional effect becomes TRUE, the conditional
                            // effect is removed because it does not lead to any state transition.
                            this.getChildren().remove(i);
                            simplified = true;
                        } else {
                            i++;
                        }
                    } else {
                        i++;
                    }
                }
                // Finally, if the conjunction is empty, the expression becomes TRUE.
                if (this.getChildren().isEmpty()) {
                    this.setConnective(PDDLConnective.TRUE);
                    simplified = true;
                } else if (this.getChildren().size() == 1) {
                    this.assign(this.getChildren().get(0));
                    simplified = true;
                }
                break;
            case OR:
                i = 0;
                while (i < this.getChildren().size() && this.getConnective().equals(PDDLConnective.OR)) {
                    final Expression<T> ei = this.getChildren().get(i);
                    simplified &= ei.simplify();
                    // If a child expression is TRUE, the whole disjunction is TRUE.
                    if (ei.getConnective().equals(PDDLConnective.TRUE)) {
                        this.setConnective(PDDLConnective.TRUE);
                        simplified = true;
                    } else if (ei.getConnective().equals(PDDLConnective.OR)) {
                        // If the child expression to add is a disjunction, we can simplify the expression by
                        // removing the inner disjunction.
                        this.getChildren().remove(i);
                        simplified = true;
                        int j = 0;
                        int added = 0;
                        while (j < ei.getChildren().size() && this.getConnective().equals(PDDLConnective.OR)) {
                            final Expression<T> ej = ei.getChildren().get(j);
                            if (ej.getConnective().equals(PDDLConnective.TRUE)) {
                                this.setConnective(PDDLConnective.TRUE);
                            } else if (!ej.getConnective().equals(PDDLConnective.FALSE)) {
                                this.getChildren().add(i + added, ej);
                                added++;
                            }
                            j++;
                        }
                        i += added + 1;
                    } else if (ei.getConnective().equals(PDDLConnective.WHEN)) {
                        // Simplification of the conditional expression.
                        final Expression<T> antecedent = ei.getChildren().get(0);
                        final Expression<T> consequent = ei.getChildren().get(1);
                        // If the antecedent of a conditional effect becomes FALSE , the conditional effect is
                        // removed from the action. In this case, the effect is never applicable because it
                        // requires FALSE to hold, i.e., the state must be inconsistent.
                        if (antecedent.getConnective().equals(PDDLConnective.FALSE)) {
                            this.getChildren().remove(i);
                        } else if (antecedent.getConnective().equals(PDDLConnective.TRUE)) {
                            // If the antecedent of a conditional effect becomes TRUE, the conditional effect
                            // becomes unconditional.
                            if (consequent.getConnective().equals(PDDLConnective.OR)) {
                                this.getChildren().remove(i);
                                int j = 0;
                                int added = 0;
                                while (j < consequent.getChildren().size()
                                        && this.getConnective().equals(PDDLConnective.OR)) {
                                    final Expression<T> ej = consequent.getChildren().get(j);
                                    if (ej.getConnective().equals(PDDLConnective.TRUE)) {
                                        this.setConnective(PDDLConnective.TRUE);
                                    } else if (!ej.getConnective().equals(PDDLConnective.FALSE)) {
                                        this.getChildren().add(i + added, ej);
                                        added++;
                                    }
                                    j++;
                                }
                                simplified = true;
                                i += added + 1;
                            } else {
                                this.getChildren().set(i, consequent);
                                i++;
                                simplified = true;
                            }
                        } else if (consequent.getConnective().equals(PDDLConnective.TRUE)) {
                            // If the consequent of a conditional effect becomes TRUE, the conditional
                            // effect is removed because it does not lead to any state transition.
                            this.getChildren().remove(i);
                            simplified = true;
                        } else {
                            i++;
                        }
                    } else {
                        i++;
                    }
                }
                // Finally, if the disjunction is empty, the expression becomes TRUE.
                if (this.getChildren().isEmpty()) {
                    this.setConnective(PDDLConnective.TRUE);
                    simplified = true;
                } else if (this.getChildren().size() == 1) {
                    this.assign(this.getChildren().get(0));
                    simplified = true;
                } else {
                    final Iterator<Expression<T>> it = this.getChildren().iterator();
                    while (it.hasNext()) {
                        if (it.next().getConnective().equals(PDDLConnective.FALSE)) {
                            it.remove();
                            simplified = true;
                        }
                    }
                    if (this.getChildren().isEmpty()) {
                        this.setConnective(PDDLConnective.FALSE);
                        simplified = true;
                    }
                }
                break;
            case IMPLY:
                // replace imply expression (imply p q) by its equivalent disjunction (or (not p) q)
                this.setConnective(PDDLConnective.OR);
                final Expression notp = new Expression<>(PDDLConnective.NOT);
                notp.addChild(this.getChildren().get(0));
                this.getChildren().set(0, notp);
                simplified &= this.simplify();
                break;
            case FORALL:
            case EXISTS:
            case AT_START:
            case AT_END:
            case OVER_ALL:
            case AT_END_CONSTRAINT:
            case ALWAYS_CONSTRAINT:
            case AT_MOST_ONCE_CONSTRAINT:
            case SOMETIME_CONSTRAINT:
            case WITHIN_CONSTRAINT:
            case HOLD_AFTER_CONSTRAINT:
            case HOLD_AFTER_METHOD_CONSTRAINT:
            case HOLD_BEFORE_METHOD_CONSTRAINT:
            case AT_END_METHOD_CONSTRAINT:
            case AT_START_METHOD_CONSTRAINT:
            case ALWAYS_METHOD_CONSTRAINT:
            case AT_MOST_ONCE_METHOD_CONSTRAINT:
            case SOMETIME_METHOD_CONSTRAINT:
            case SOMETIME_BEFORE_METHOD_CONSTRAINT:
            case SOMETIME_AFTER_METHOD_CONSTRAINT:
            case HOLD_BETWEEN_METHOD_CONSTRAINT:
            case HOLD_DURING_METHOD_CONSTRAINT:
                simplified &= this.getChildren().get(0).simplify();
                if (this.getChildren().get(0).getConnective().equals(PDDLConnective.TRUE)) {
                    this.setConnective(PDDLConnective.TRUE);
                } else if (this.getChildren().get(0).getConnective().equals(PDDLConnective.FALSE)) {
                    this.setConnective(PDDLConnective.FALSE);
                }
                break;
            case NOT:
                final Expression<T> neg = this.getChildren().get(0);
                simplified &= neg.simplify();
                if (neg.getConnective().equals(PDDLConnective.TRUE)) {
                    this.setConnective(PDDLConnective.FALSE);
                } else if (neg.getConnective().equals(PDDLConnective.FALSE)) {
                    this.setConnective(PDDLConnective.TRUE);
                }
                break;
            case WHEN:
            case SOMETIME_AFTER_CONSTRAINT: // Simplification must be checked with the constraints semantic
            case SOMETIME_BEFORE_CONSTRAINT:
                simplified &= this.getChildren().get(0).simplify();
                simplified &= this.getChildren().get(1).simplify();
                break;
            case ALWAYS_WITHIN_CONSTRAINT:
                simplified &= this.getChildren().get(0).simplify();
                simplified &= this.getChildren().get(1).simplify();
                simplified &= this.getChildren().get(2).simplify();
                break;
            case HOLD_DURING_CONSTRAINT:
                if (this.getChildren().get(0).getValue() > this.getChildren().get(1).getValue()) {
                    this.setConnective(PDDLConnective.FALSE);
                    simplified = true;
                } else {
                    Expression<T> child = this.getChildren().get(0);
                    simplified &= child.simplify();
                    if (child.getConnective().equals(PDDLConnective.TRUE)
                        || child.getConnective().equals(PDDLConnective.FALSE)) {
                        this.setConnective(child.getConnective());
                        simplified = true;
                    }
                }
                break;
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case NUMBER:
            case TASK_ID:
            case ATOM:
            case FN_HEAD:
            case TRUE:
            case FALSE:
            case TASK:
                break;
            default:
                throw new UnexpectedExpressionException(this.getConnective().toString());
        }
        return simplified;
    }

    /**
     * Removed duplicated child in conjunction and disjunction expressions. The expression in parameter is
     * modified. If a duplicated subexpression is found, the duplicated expression is removed.
     *
     * @return <code>true</code> if the expression was not modified; <code>false</code> otherwise.
     */
    private final boolean removeDuplicateChild() {
        assert this.getConnective().equals(PDDLConnective.AND)
            || this.getConnective().equals(PDDLConnective.OR);
        boolean modified = false;
        for (int i = 0; i < this.getChildren().size(); i++) {
            final Expression ei =  this.getChildren().get(i);
            for (int j = i + 1; j < this.getChildren().size(); j++) {
                final Expression ej = this.getChildren().get(j);
                if (ei.equals(ej)) {
                    this.getChildren().remove(j);
                    j--;
                    modified = true;
                }
            }
        }
        return modified;
    }

    /**
     * Removes tautologies of the form (a and not a) in conjunctive and disjunctive expressions. The expression
     * in parameter is modified. If a tautology is detected, the subexpression of the tautology are removed and replaced
     * by a TRUE expression.
     *
     * @return <code>true</code> if the expression was not modified; <code>false</code> otherwise.
     */
    private final boolean removedTautology() {
        assert this.getConnective().equals(PDDLConnective.AND)
            || this.getConnective().equals(PDDLConnective.OR);
        boolean modified = false;
        for (int i = 0; i < this.getChildren().size(); i++) {
            final Expression ei = this.getChildren().get(i);
            final Expression neg = new Expression<>(PDDLConnective.NOT);
            neg.addChild(ei);
            for (int j = i + 1; j < this.getChildren().size(); j++) {
                final Expression ej = this.getChildren().get(j);
                if (ej.equals(neg)) {
                    ei.setConnective(PDDLConnective.TRUE);
                    this.getChildren().remove(j);
                    j--;
                    modified = true;
                }
            }
        }
        return modified;
    }

    /**
     * Returns if a specified expression is contains, i.e., is a sub-expression of this expression. More
     * formally, returns <code>true</code> if and only if this expression contains at least one
     * subexpression <code>s</code> such that <code>s.equals(exp)</code>.
     *
     * @param exp the expression to test.
     * @return <code>true</code> if the specified expression <code>exp</code> is a sub-expression of
     *          this expression; <code>false</code> otherwise.
     */
    public final boolean contains(final Expression<T> exp) {
        for (Expression s : this.getChildren()) {
            if (s.equals(exp) || s.contains(exp)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Removes all the occurrences of a specified expression contained in this expression and
     * returns <code>true</code> if and only if at least one occurrence was removed.
     *
     * @param exp the expression to remove.
     * @return <code>true</code> if the specified expression <code>exp</code> was removed;
     *          <code>false</code> otherwise.
     */
    public final boolean remove(final Expression<T> exp) {
        boolean removed = false;
        Iterator<Expression<T>> it = this.getChildren().iterator();
        while (it.hasNext()) {
            Expression s = it.next();
            if (s.equals(exp)) {
                it.remove();
                removed = true;
            } else {
                removed = removed || s.remove(exp);
            }
        }
        return removed;
    }

    /**
     * Returns if the expression is equal to another object. The primitive flag and the task id are not used for
     * comparison.
     *
     * @param object the other object.
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object object) {
        if (this == object) return true;
        if (object != null && object instanceof Expression) {
            final Expression<T> other = (Expression<T>) object;
            return Objects.equals(this.getConnective(), other.getConnective())
                && Objects.equals(this.getSymbol(), other.getSymbol())
                && Objects.equals(this.getArguments(), other.getArguments())
                && Objects.equals(this.getValue(), other.getValue())
                && Objects.equals(this.getQuantifiedVariables(), other.getQuantifiedVariables())
                && Objects.equals(this.getVariable(), other.getVariable())
                && Objects.equals(this.getChildren(), other.getChildren());
        }
        return false;
    }

    /**
     * Returns the hash code value of the expression.
     *
     * @return the hash code value of the expression.
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return Objects.hash(this.getConnective(), this.getSymbol(), this.getArguments(), this.getValue(),
            this.getQuantifiedVariables(), this.getVariable(), this.getChildren());
    }

    /**
     * Returns if this expression is malformed. An expression is considered as well in the following cases:
     * <ul>
     * <li>OR and AND expressions have to have all their child well-formed.</li>
     * <li>EQUAL_ATOM expressions are well-formed if the expression contains an atom of at least two symbols.</li>
     * <li>Quantified expressions (EXISTS, FORALL) is well formed if it has at least one quantified variable and one
     * child expression.</li>
     * <li>IMPLY, WHEN, EQUAL_COMPARISON, LESS_COMPARISON, LESS_OR_EQUAL_COMPARISON, GREATER_COMPARISON,
     * GREATER_OR_EQUAL_COMPARISON, ASSIGN, INCREASE, DECREASE, SCALE_UP, SCALE_DOWN, MULTIPLICATION, DIVISION, MINUS,
     * PLUS, SOMETIME_AFTER_CONSTRAINT, SOMETIME_BEFORE_CONSTRAINT expressions are well-formed if they have to child and
     * both child are well-formed.</li>
     * <li> NOT, UMINUS, AT_START, AT_END, OVER_ALL, MINIMIZE, MAXIMIZE, F_EXP_T, F_EXP, AT_END_METHOD_CONSTRAINT,
     * AT_START_METHOD_CONSTRAINT, ALWAYS_METHOD_CONSTRAINT, AT_MOST_ONCE_METHOD_CONSTRAINT, SOMETIME_METHOD_CONSTRAINT
     * expression are well-formed if they have on child and if it is well-formed.</li>
     * <li>ATOM, TASKS, and F_HEAD expressions without any symbols as arguments are considered as well formed.</li>
     * <li>TIMED_LITERAL, WITHIN_CONSTRAINT, HOLD_AFTER_CONSTRAINT, HOLD_BEFORE_METHOD_CONSTRAINT,
     * HOLD_AFTER_METHOD_CONSTRAINT, SOMETIME_BEFORE_METHOD_CONSTRAINT,
     * SOMETIME_AFTER_METHOD_CONSTRAINT expressions are considered as well-formed if they have well-formed child and a
     * time value.</li>
     * <li>HOLD_DURING_CONSTRAINT, HOLD_BETWEEN_METHOD_CONSTRAINT, HOLD_DURING_METHOD_CONSTRAINT expressions are
     * well-formed if they have two child well-formed and an time interval value.</li>
     * <li>ALWAYS_WITHIN expression must have at least two children to be considered as well formed and time interval
     * value.</li>.
     * <li>NUMBER expressions are considered is they have a value.</li>
     * <li>TIME_VAR, IS_VIOLATED exprssions are always considered as well-formed</li>
     * </ul>
     *
     * @return <code>true</code> if the expression is malformed; <code>false</code> otherwise.
     */
    public final boolean isMalformedExpression() {
        boolean malformed = false;
        switch (this.getConnective()) {
            case AND:
            case OR:
                Iterator<Expression<T>> i = this.getChildren().iterator();
                while (!malformed && i.hasNext()) {
                    malformed |= i.next().isMalformedExpression();
                }
                break;
            case EQUAL_ATOM:
                malformed = this.getArguments().size() != 2;
                break;
            case FORALL:
            case EXISTS:
                malformed = this.getQuantifiedVariables().isEmpty()
                    || this.getChildren().isEmpty()
                    || this.getChildren().get(0).isMalformedExpression();
                break;
            case IMPLY:
            case WHEN:
            case EQUAL_COMPARISON:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case ASSIGN:
            case INCREASE:
            case DECREASE:
            case SCALE_UP:
            case SCALE_DOWN:
            case MULTIPLICATION:
            case DIVISION:
            case MINUS:
            case PLUS:
            case SOMETIME_AFTER_CONSTRAINT:
            case SOMETIME_BEFORE_CONSTRAINT:
                malformed = this.getChildren().size() != 2
                    || this.getChildren().get(0).isMalformedExpression()
                    || this.getChildren().get(1).isMalformedExpression();
                break;
            case NOT:
            case UMINUS:
            case AT_START:
            case AT_END:
            case OVER_ALL:
            case MINIMIZE:
            case MAXIMIZE:
            case F_EXP_T:
            case F_EXP:
            case AT_END_CONSTRAINT:
            case ALWAYS_CONSTRAINT:
            case AT_MOST_ONCE_CONSTRAINT:
            case SOMETIME_CONSTRAINT:
            case AT_END_METHOD_CONSTRAINT:
            case AT_START_METHOD_CONSTRAINT:
            case ALWAYS_METHOD_CONSTRAINT:
            case AT_MOST_ONCE_METHOD_CONSTRAINT:
            case SOMETIME_METHOD_CONSTRAINT:
                malformed = this.getChildren().size() != 1
                    || this.getChildren().get(0).isMalformedExpression();
                break;
            case ATOM:
            case TASK:
            case FN_HEAD:
                malformed = this.getSymbol() == null;
                break;
            case TIMED_LITERAL:
            case WITHIN_CONSTRAINT:
            case HOLD_AFTER_CONSTRAINT:
                malformed = this.getChildren().size() != 2
                    || !this.getChildren().get(0).getConnective().equals(PDDLConnective.NUMBER)
                    || this.getChildren().get(1).isMalformedExpression();
                break;
            case HOLD_BEFORE_METHOD_CONSTRAINT:
            case HOLD_AFTER_METHOD_CONSTRAINT:
            case SOMETIME_BEFORE_METHOD_CONSTRAINT:
            case SOMETIME_AFTER_METHOD_CONSTRAINT:
                malformed = this.getChildren().size() != 2
                    || !this.getChildren().get(0).getConnective().equals(PDDLConnective.TASK_ID)
                    || this.getChildren().get(1).isMalformedExpression();
                break;
            case HOLD_DURING_CONSTRAINT:
                malformed = this.getChildren().size() != 3
                    || !this.getChildren().get(0).getConnective().equals(PDDLConnective.NUMBER)
                    || !this.getChildren().get(1).getConnective().equals(PDDLConnective.NUMBER)
                    || this.getChildren().get(2).isMalformedExpression();
                break;
            case HOLD_BETWEEN_METHOD_CONSTRAINT:
            case HOLD_DURING_METHOD_CONSTRAINT:
                malformed = this.getChildren().size() != 3
                    || !this.getChildren().get(0).getConnective().equals(PDDLConnective.TASK_ID)
                    || !this.getChildren().get(1).getConnective().equals(PDDLConnective.TASK_ID)
                    || this.getChildren().get(2).isMalformedExpression();
                break;
            case ALWAYS_WITHIN_CONSTRAINT:
                malformed = this.getChildren().size() != 4
                    || !this.getChildren().get(0).getConnective().equals(PDDLConnective.NUMBER)
                    || !this.getChildren().get(1).getConnective().equals(PDDLConnective.NUMBER)
                    || this.getChildren().get(2).isMalformedExpression()
                    || this.getChildren().get(3).isMalformedExpression();
                break;
            case NUMBER:
                malformed = this.getValue() == null;
                break;
            case TASK_ID:
                malformed = this.getTaskID() == null;
                break;
            case TIME_VAR:
            case IS_VIOLATED:
            case TRUE:
            case FALSE:
                break;
            case LESS_ORDERING_CONSTRAINT:
            case LESS_OR_EQUAL_ORDERING_CONSTRAINT:
            case GREATER_ORDERING_CONSTRAINT:
            case GREATER_OR_EQUAL_ORDERING_CONSTRAINT:
            case EQUAL_ORDERING_CONSTRAINT:
                malformed = this.getChildren().size() != 2
                    && this.getChildren().get(0).getConnective().equals(PDDLConnective.TASK_ID)
                    && this.getChildren().get(0).isMalformedExpression()
                    && this.getChildren().get(1).getConnective().equals(PDDLConnective.TASK_ID)
                    && this.getChildren().get(1).isMalformedExpression();
                break;
            default:
                throw new UnexpectedExpressionException(this.getConnective().toString());

        }
        return malformed;
    }

    /**
     * Returns a string representation of this node.
     *
     * @return a string representation of this node.
     * @see java.lang.Object#toString
     */
    @Override
    public String toString() {
        return this.toString("");
    }

    /**
     * Returns a string representation of this parser node.
     *
     * @param baseOffset the offset white space from the left used for indentation.
     * @return a string representation of this parser node.
     * @throws MalformedExpressionException if the expression is malformed.
     */
    public String toString(String baseOffset) throws MalformedExpressionException {
        if (this.isMalformedExpression()) {
            throw new MalformedExpressionException("Expression " + this.getConnective() + " is malformed");
        }
        StringBuilder str = new StringBuilder();
        switch (this.getConnective()) {
            case ATOM:
            case FN_HEAD:
                str.append("(");
                str.append(this.getSymbol());
                str.append(" ");
                if (!this.getArguments().isEmpty()) {
                    for (int i = 0; i < this.getArguments().size() - 1; i++) {
                        str.append(this.getArguments().get(i).toString()).append(" ");
                    }
                    str.append(this.getArguments().get(this.getArguments().size() - 1).toString());
                }
                str.append(")");
                break;
            case TASK:
                str.append("(");
                str.append(this.getSymbol());
                str.append(" ");
                if (!this.getArguments().isEmpty()) {
                    if (this.getTaskID() != null) {
                        str.append(this.getTaskID()).append(" (");
                    }
                    for (int i = 0; i < this.getArguments().size() - 1; i++) {
                        str.append(this.getArguments().get(i).toString()).append(" ");
                    }
                    str.append(this.getArguments().get(this.getArguments().size() - 1).toString());
                }
                str.append(")");
                break;
            case EQUAL_ATOM:
                str.append("(")
                    .append(this.getConnective().getImage())
                    .append(" ");
                for (int i = 0; i < this.getArguments().size() - 1; i++) {
                    str.append(this.getArguments().get(i).toString()).append(" ");
                }
                str.append(this.getArguments().get(this.getArguments().size() - 1).toString()).append(")");
                break;
            case AND:
            case OR:
                if (!this.getChildren().isEmpty()) {
                    String offset = baseOffset + "  ";
                    str.append("(").append(this.getConnective().getImage());
                    str.append(" ");
                    for (int i = 0; i < this.getChildren().size() - 1; i++) {
                        str.append(this.getChildren().get(i).toString(offset)).append("\n").append(offset);
                    }
                    str.append(this.getChildren().get(this.getChildren().size() - 1).toString(offset));
                    str.append(")");
                } else {
                    str.append("()");
                }
                break;
            case IMPLY:
                str.append("(");
                str.append(this.getConnective().getImage());
                str.append(" ");
                str.append(this.getChildren().get(0).toString(baseOffset));
                str.append(" ");
                str.append(this.getChildren().get(1).toString(baseOffset));
                str.append(")");
                break;
            case FORALL:
            case EXISTS:
                String off = baseOffset + baseOffset + "  ";
                str.append(" (");
                str.append(this.getConnective().getImage());
                str.append(" (");
                if (!this.getQuantifiedVariables().isEmpty()) {
                    for (int i = 0; i < this.getQuantifiedVariables().size() - 1; i++) {
                        str.append(this.getQuantifiedVariables().get(i).toString());
                        str.append(", ");
                    }
                    str.append(this.getQuantifiedVariables().get(this.getQuantifiedVariables().size() - 1).toString());
                }
                str.append(")\n");
                str.append(off);
                str.append(this.children.get(0).toString(off));
                str.append(")");
                break;
            case NUMBER:
                str.append(this.value);
                break;
            case F_EXP:
                str.append(this.children.get(0).toString(baseOffset));
                break;
            case F_EXP_T:
                if (this.children.isEmpty()) {
                    str.append(this.getVariable());
                } else {
                    str.append("(").append(this.getConnective().getImage()).append(" ")
                        .append(this.getVariable()).append(" ")
                        .append(this.children.get(0).toString(baseOffset));
                }
                break;
            case TIME_VAR:
                str.append(this.getVariable());
                break;
            case FN_ATOM:
            case WHEN:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case ASSIGN:
            case INCREASE:
            case DECREASE:
            case SCALE_UP:
            case SCALE_DOWN:
            case MULTIPLICATION:
            case DIVISION:
            case MINUS:
            case PLUS:
            case SOMETIME_AFTER_CONSTRAINT:
            case SOMETIME_BEFORE_CONSTRAINT:
                str.append("(");
                str.append(this.getConnective().getImage()).append(" ");
                str.append(this.children.get(0).toString(baseOffset)).append(" ");
                str.append(this.children.get(1).toString(baseOffset));
                str.append(")");
                break;
            case LESS_ORDERING_CONSTRAINT:
            case LESS_OR_EQUAL_ORDERING_CONSTRAINT:
            case GREATER_ORDERING_CONSTRAINT:
            case GREATER_OR_EQUAL_ORDERING_CONSTRAINT:
            case EQUAL_ORDERING_CONSTRAINT:
                str.append("(");
                str.append(this.getConnective().getImage()).append(" ");
                str.append(this.arguments.get(0).toString()).append(" ");
                str.append(this.arguments.get(1).toString());
                str.append(")");
                break;
            case NOT:
            case UMINUS:
            case AT_START:
            case AT_END:
            case OVER_ALL:
            case AT_END_CONSTRAINT:
            case ALWAYS_CONSTRAINT:
            case SOMETIME_CONSTRAINT:
            case AT_MOST_ONCE_CONSTRAINT:
            case AT_END_METHOD_CONSTRAINT:
            case AT_START_METHOD_CONSTRAINT:
            case ALWAYS_METHOD_CONSTRAINT:
            case AT_MOST_ONCE_METHOD_CONSTRAINT:
            case SOMETIME_METHOD_CONSTRAINT:
                str.append("(");
                str.append(this.getConnective().getImage()).append(" ");
                str.append(this.getChildren().get(0).toString(baseOffset));
                str.append(")");
                break;
            case MINIMIZE:
            case MAXIMIZE:
                str.append(this.getConnective().getImage()).append(" ")
                    .append(this.getChildren().get(0).getValue())
                    .append(")");
                break;
            case IS_VIOLATED:
                str.append("(").append(this.getConnective().getImage()).append(")");
                break;
            case TIMED_LITERAL:
            case WITHIN_CONSTRAINT:
            case HOLD_AFTER_CONSTRAINT:
            case HOLD_BEFORE_METHOD_CONSTRAINT:
            case HOLD_AFTER_METHOD_CONSTRAINT:
            case SOMETIME_BEFORE_METHOD_CONSTRAINT:
            case SOMETIME_AFTER_METHOD_CONSTRAINT:
                str.append("(");
                str.append(this.getConnective().getImage()).append(" ");
                str.append(this.getChildren().get(0).toString()).append(" ");
                str.append(this.getChildren().get(1).toString(baseOffset));
                str.append(")");
                break;
            case HOLD_DURING_CONSTRAINT:
            case HOLD_BETWEEN_METHOD_CONSTRAINT:
            case HOLD_DURING_METHOD_CONSTRAINT:
                str.append("(");
                str.append(this.getConnective().getImage()).append(" ");
                str.append(this.getChildren().get(0).toString()).append(" ");
                str.append(this.getChildren().get(1).toString()).append(" ");
                str.append(this.getChildren().get(2).toString(baseOffset));
                str.append(")");
                break;
            case ALWAYS_WITHIN_CONSTRAINT:
                str.append("(");
                str.append(this.getConnective().getImage()).append(" ");
                str.append(this.getChildren().get(0).toString()).append(" ");
                str.append(this.getChildren().get(1).toString()).append(" ");
                str.append(this.getChildren().get(2).toString(baseOffset));
                str.append(this.getChildren().get(3).toString(baseOffset));
                str.append(")");
                break;
            case TASK_ID:
                str.append(this.getTaskID().toString());
                break;
            case TIMED_TASK_ID:
                str.append("( ");
                str.append(this.getTimeSpecifier());
                str.append(" ");
                str.append(this.getTaskID().getImage());
                str.append(")");
                break;
            default:
                throw new UnexpectedExpressionException(this.getConnective().toString());

        }
        return str.toString();
    }

    /**
     * Convert an expression in conjunctive normal form (CNF).
     */
    public void toCNF() throws UnexpectedExpressionException {
        switch (this.getConnective()) {
            case WHEN:
                final Expression<T> antecedent = this.getChildren().get(0);
                final Expression<T> consequence = this.getChildren().get(1);
                antecedent.toDNF();
                this.setConnective(PDDLConnective.AND);
                this.getChildren().clear();
                for (Expression<T> ei : antecedent.getChildren()) {
                    final Expression<T> newWhen = new Expression<>(PDDLConnective.WHEN);
                    newWhen.getChildren().add(ei);
                    newWhen.getChildren().add(new Expression<>(consequence));
                    this.getChildren().add(newWhen);
                }
                break;
            case AND:
                final List<Expression<T>> children = this.getChildren();
                int i = 0;
                while (i < children.size()) {
                    final Expression<T> ei = children.get(i);
                    ei.toCNF();
                    this.getChildren().remove(i);
                    for (Expression<T> ej : ei.getChildren()) {
                        this.getChildren().add(i, ej);
                        i++;
                    }
                }
                break;
            case ATOM:
            case AT_END:
            case AT_START:
            case OVER_ALL:
            case INCREASE:
            case DECREASE:
            case ASSIGN:
            case SCALE_UP:
            case SCALE_DOWN:
            case NOT:
            case TRUE:
                Expression<T> copy = new Expression<T>(this);
                this.setConnective(PDDLConnective.AND);
                this.getChildren().clear();
                this.getChildren().add(copy);
                break;
            default:
                throw new UnexpectedExpressionException(this.getConnective().toString());
        }
    }

    /**
     * Convert an expression in disjunctive normal form (DNF).
     *
     */
    public void toDNF() throws UnexpectedExpressionException {
        switch (this.getConnective()) {
            case OR:
                List<Expression<T>> children = this.getChildren();
                int index = 0;
                while (index < children.size()) {
                    final Expression<T> ei = children.get(index);
                    ei.toDNF();
                    if (ei.getConnective().equals(PDDLConnective.OR)) {
                        children.remove(index);
                        for (Expression<T> ej : ei.getChildren()) {
                            children.add(index, ej);
                            index++;
                        }
                    }
                }
                break;
            case AND:
                children = this.getChildren();
                for (Expression<T> child : children) {
                    child.toDNF();
                }
                Expression<T> dnf = this.getChildren().get(0);
                for (int i = 1; i < this.getChildren().size(); i++) {
                    final Expression<T> orExp = this.getChildren().get(i);
                    final Expression<T> newOr = new Expression<>(PDDLConnective.OR);
                    for (Expression<T> newAnd : dnf.getChildren()) {
                        for (Expression<T> ek : orExp.getChildren()) {
                            ek.getChildren().stream().filter(el -> !newAnd.getChildren().contains(el)).forEach(el -> {
                                if (el.getConnective().equals(PDDLConnective.OR)
                                    || el.getConnective().equals(PDDLConnective.AND)
                                    && el.getChildren().size() == 1) {
                                    newAnd.getChildren().add(el.getChildren().get(0));
                                } else {
                                    newAnd.getChildren().add(el);
                                }
                            });
                            boolean add = true;
                            for (Expression<T> el : newAnd.getChildren()) {
                                if (el.getConnective().equals(PDDLConnective.FALSE)) {
                                    add = false;
                                    break;
                                }
                            }
                            if (add) {
                                if (newAnd.getChildren().size() == 1) {
                                    newOr.getChildren().add(newAnd.getChildren().get(0));
                                } else {
                                    newOr.getChildren().add(newAnd);
                                }
                            }
                        }
                    }
                    dnf = newOr;
                }
                this.assign(dnf);
                break;
            case ATOM:
            case NOT:
            case LESS_COMPARISON:
            case LESS_OR_EQUAL_COMPARISON:
            case GREATER_COMPARISON:
            case GREATER_OR_EQUAL_COMPARISON:
            case EQUAL_COMPARISON:
            case EQUAL_ATOM:
            case INCREASE:
            case DECREASE:
            case SCALE_UP:
            case SCALE_DOWN:
            case AT_END:
            case AT_START:
            case OVER_ALL:
            case FALSE:
            case TRUE:
                Expression<T> and = new Expression<>(PDDLConnective.AND);
                and.getChildren().add(new Expression<>(this));
                this.setConnective(PDDLConnective.OR);
                this.getChildren().clear();
                this.getChildren().add(and);
                break;
            default:
                throw new UnexpectedExpressionException(this.getConnective().toString());
        }
    }

    /**
     * Returns the set of task IDs contains in this expression.
     *
     * @return the set of task IDs contains in exp.
     * @throws UnexpectedExpressionException if the expression is not a TASK, F_TASK_TIME,
     *      LESS_ORDERING_CONSTRAINT, LESS_OR_EQUAL_ORDERING_CONSTRAINT, GREATER_ORDERING_CONSTRAINT,
     *      GREATER_OR_EQUAL_ORDERING_CONSTRAINT, EQUAL_ORDERING_CONSTRAINT, HOLD_BEFORE_METHOD_CONSTRAINT,
     *      HOLD_AFTER_METHOD_CONSTRAINT, SOMETIME_BEFORE_METHOD_CONSTRAINT, SOMETIME_AFTER_METHOD_CONSTRAINT,
     *      HOLD_BETWEEN_METHOD_CONSTRAINT, HOLD_DURING_METHOD_CONSTRAINT OR AND.
     */
    public static Set<Symbol<String>> getTaskIDs(Expression<String> exp) throws UnexpectedExpressionException {
        Set<Symbol<String>> taskIDs  = new HashSet<Symbol<String>>();
        switch (exp.getConnective()) {
            case TASK:
                if (exp.getTaskID() != null) {
                    taskIDs.add(exp.getTaskID());
                }
                break;
            case TASK_ID:
                taskIDs.add(exp.getTaskID());
                break;
            case F_TASK_TIME:
                taskIDs.add(exp.getArguments().get(0)); // Add constraints HDDL2.1
                break;
            case NOT:
                if (!exp.getChildren().get(0).getConnective().equals(PDDLConnective.EQUAL_ATOM)) {
                    throw new UnexpectedExpressionException(exp.getConnective().toString());
                }
                break;
            case AND:
            case LESS_ORDERING_CONSTRAINT:
            case LESS_OR_EQUAL_ORDERING_CONSTRAINT: // Add method ordering HDDL2.1
            case GREATER_ORDERING_CONSTRAINT: // Add method ordering HDDL2.1
            case GREATER_OR_EQUAL_ORDERING_CONSTRAINT: // Add method ordering HDDL2.1
            case EQUAL_ORDERING_CONSTRAINT: // Add method ordering HDDL2.1
            case HOLD_BEFORE_METHOD_CONSTRAINT: // Add method ordering HDDL2.1
            case HOLD_AFTER_METHOD_CONSTRAINT: // Add method ordering HDDL2.1
            case SOMETIME_BEFORE_METHOD_CONSTRAINT: // Add method ordering HDDL2.1
            case SOMETIME_AFTER_METHOD_CONSTRAINT: // Add method ordering HDDL2.1
            case HOLD_BETWEEN_METHOD_CONSTRAINT: // Add method ordering HDDL2.1
            case HOLD_DURING_METHOD_CONSTRAINT: // Add method ordering HDDL2.1
                for (int i = 0; i < exp.getChildren().size(); i++) {
                    final Expression<String> c = exp.getChildren().get(i);
                    taskIDs.addAll(Expression.getTaskIDs(c));
                }
                break;
            case AT_END_METHOD_CONSTRAINT:
            case AT_START_METHOD_CONSTRAINT:
            case ALWAYS_METHOD_CONSTRAINT:
            case AT_MOST_ONCE_METHOD_CONSTRAINT:
            case SOMETIME_METHOD_CONSTRAINT:
            case EQUAL_ATOM:
                // Do nothing
                break;
            default:
                throw new UnexpectedExpressionException(exp.getConnective().toString());
        }
        return taskIDs;
    }

    public final boolean isLeaf() {
        return this.getConnective().equals(PDDLConnective.ATOM)
            || this.getConnective().equals(PDDLConnective.TASK)
            || this.getConnective().equals(PDDLConnective.FN_HEAD)
            || this.getConnective().equals(PDDLConnective.EQUAL_ATOM);
    }

    @Override
    public Iterator<Expression<T> > iterator() {
        return new PreOrderIterator(this);
    }

    private class PreOrderIterator implements Iterator<Expression<T> > {

        Stack<Expression<T>> stack = new Stack<>();

        public PreOrderIterator(Expression<T> expression) {
            if (expression.isLeaf()) {
                this.stack.push(expression);
            } else {
                this.stack.addAll(expression.getChildren());
            }
        }

        @Override
        public boolean hasNext() {
            return !this.stack.isEmpty();
        }

        @Override
        public Expression<T> next() {
            Expression<T> expression = stack.remove(0);
            stack.addAll(expression.getChildren());
            return expression;
        }
    }
}

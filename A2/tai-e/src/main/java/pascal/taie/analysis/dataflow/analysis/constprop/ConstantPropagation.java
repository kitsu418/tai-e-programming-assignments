/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Map;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        return null;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return null;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        CPFact target_backup = target.copy();
        target_backup.forEach((var, value) -> {
            target.update(var, meetValue(value, fact.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isConstant()) {
            return v1.getConstant() == v2.getConstant() ? v1 : Value.getNAC();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt<?, ?>) {
            RValue exp = ((DefinitionStmt<?, ?>) stmt).getRValue();
            Var var = (Var) ((DefinitionStmt<?, ?>) stmt).getLValue();
            out.copyFrom(in);
            out.remove(var);
            switch (exp.getType().getName()) {
                case "Var" -> out.update(var, in.get((Var) exp));
                case "IntLiteral" -> out.update(var, Value.makeConstant(((IntLiteral) exp).getValue()));
                case "BinaryExp" -> out.update(var, evaluate(exp, in));
            }
            return !in.equals(out);
        } else {
            return out.copyFrom(in);
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            if (canHoldInt(operand1) && canHoldInt(operand2)) {
                if (in.get(operand1).isConstant() && in.get(operand2).isConstant()) {
                    IntLiteral literal1 = (IntLiteral) operand1.getTempConstValue();
                    IntLiteral literal2 = (IntLiteral) operand1.getTempConstValue();
                    if (exp instanceof ArithmeticExp) {
                        return switch (((ArithmeticExp) exp).getOperator()) {
                            case ADD -> Value.makeConstant(literal1.getValue() + literal2.getValue());
                            case SUB -> Value.makeConstant(literal1.getValue() - literal2.getValue());
                            case MUL -> Value.makeConstant(literal1.getValue() * literal2.getValue());
                            case DIV ->
                                    literal2.getValue() == 0 ? Value.getUndef() : Value.makeConstant(literal1.getValue() / literal2.getValue());
                            case REM ->
                                    literal2.getValue() == 0 ? Value.getUndef() : Value.makeConstant(literal1.getValue() % literal2.getValue());
                        };
                    } else if (exp instanceof ConditionExp) {
                        return Value.makeConstant(switch (((ConditionExp) exp).getOperator()) {
                            case EQ -> literal1.getValue() == literal2.getValue();
                            case GE -> literal1.getValue() >= literal2.getValue();
                            case GT -> literal1.getValue() > literal2.getValue();
                            case LE -> literal1.getValue() <= literal2.getValue();
                            case LT -> literal1.getValue() < literal2.getValue();
                            case NE -> literal1.getValue() != literal2.getValue();
                        } ? 1 : 0);
                    } else if (exp instanceof ShiftExp) {
                        return Value.makeConstant(switch (((ShiftExp) exp).getOperator()) {
                            case SHL -> literal1.getValue() << literal2.getValue();
                            case SHR -> literal1.getValue() >> literal2.getValue();
                            case USHR -> literal1.getValue() >>> literal2.getValue();
                        });
                    } else if (exp instanceof BitwiseExp) {
                        return Value.makeConstant(switch (((BitwiseExp) exp).getOperator()) {
                            case OR -> literal1.getValue() | literal2.getValue();
                            case AND -> literal1.getValue() & literal2.getValue();
                            case XOR -> literal1.getValue() ^ literal2.getValue();
                        });
                    } else {
                        return Value.getNAC();
                    }
                } else if (in.get(operand1).isNAC() && in.get(operand2).isNAC()) {
                    return Value.getNAC();
                } else {
                    return Value.getUndef();
                }
            } else {
                return Value.getNAC();
            }
        } else if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else {
            return Value.getNAC();
        }
    }
}

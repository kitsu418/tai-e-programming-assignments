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

public class ConstantPropagation extends AbstractDataflowAnalysis<Stmt, CPFact> {

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
        CPFact fact = newInitialFact();
        cfg.getIR().getParams().forEach(var -> {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isConstant()) {
            return v1.equals(v2) ? v1 : Value.getNAC();
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
        if (stmt instanceof DefinitionStmt<?, ?> st) {
            if (st.getLValue() instanceof Var var && canHoldInt(var)) {
                RValue exp = ((DefinitionStmt<?, ?>) stmt).getRValue();
                CPFact out_backup = newInitialFact();
                out_backup.copyFrom(out);
                out.copyFrom(in);
                out.update(var, evaluate(exp, in));
                return !out_backup.equals(out);
            } else {
                return out.copyFrom(in);
            }
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
                case BYTE, SHORT, INT, CHAR, BOOLEAN -> {
                    return true;
                }
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
        if (exp instanceof BinaryExp b) {
            Var operand1 = b.getOperand1();
            Var operand2 = b.getOperand2();
            if (canHoldInt(operand1) && canHoldInt(operand2)) {
                if (exp instanceof ArithmeticExp a && (a.getOperator() == ArithmeticExp.Op.DIV
                        || a.getOperator() == ArithmeticExp.Op.REM) && in.get(operand2).isConstant()
                        && in.get(operand2).getConstant() == 0) {
                    return Value.getUndef();
                }
                if (in.get(operand1).isConstant() && in.get(operand2).isConstant()) {
                    int literal1 = in.get(operand1).getConstant();
                    int literal2 = in.get(operand2).getConstant();
                    if (exp instanceof ArithmeticExp a) {
                        return switch (a.getOperator()) {
                            case ADD -> Value.makeConstant(literal1 + literal2);
                            case SUB -> Value.makeConstant(literal1 - literal2);
                            case MUL -> Value.makeConstant(literal1 * literal2);
                            case DIV -> Value.makeConstant(literal1 / literal2);
                            case REM -> Value.makeConstant(literal1 % literal2);
                        };
                    } else if (exp instanceof ConditionExp c) {
                        return Value.makeConstant(switch (c.getOperator()) {
                            case EQ -> literal1 == literal2;
                            case GE -> literal1 >= literal2;
                            case GT -> literal1 > literal2;
                            case LE -> literal1 <= literal2;
                            case LT -> literal1 < literal2;
                            case NE -> literal1 != literal2;
                        } ? 1 : 0);
                    } else if (exp instanceof ShiftExp s) {
                        return Value.makeConstant(switch (s.getOperator()) {
                            case SHL -> literal1 << literal2;
                            case SHR -> literal1 >> literal2;
                            case USHR -> literal1 >>> literal2;
                        });
                    } else if (exp instanceof BitwiseExp bi) {
                        return Value.makeConstant(switch (bi.getOperator()) {
                            case OR -> literal1 | literal2;
                            case AND -> literal1 & literal2;
                            case XOR -> literal1 ^ literal2;
                        });
                    } else {
                        return Value.getNAC();
                    }
                } else if (in.get(operand1).isNAC() || in.get(operand2).isNAC()) {
                    return Value.getNAC();
                } else {
                    return Value.getUndef();
                }
            } else {
                return Value.getNAC();
            }
        } else if (exp instanceof Var v) {
            return in.get(v);
        } else if (exp instanceof IntLiteral l) {
            return Value.makeConstant(l.getValue());
        } else {
            return Value.getNAC();
        }
    }
}

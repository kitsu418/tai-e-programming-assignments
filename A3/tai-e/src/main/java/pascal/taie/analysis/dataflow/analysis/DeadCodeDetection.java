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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        for (Stmt stmt : cfg.getNodes()) {
            System.out.printf("#%d: %s, in: %s, out: %s\n", stmt.getLineNumber(), stmt, liveVars.getInFact(stmt), liveVars.getOutFact(stmt));
        }

        boolean[] visited = new boolean[cfg.getNodes().size()];
        Stmt entry = cfg.getEntry();
        Stmt stmt;
        Queue<Stmt> worklist = new LinkedList<>();
        worklist.offer(entry);
        while (!worklist.isEmpty()) {
            stmt = worklist.remove();
            if (visited[stmt.getIndex()]) {
                continue;
            }
            visited[stmt.getIndex()] = true;
            // unreachable code, if case
            if (stmt instanceof If i) {
                ConditionExp condition = i.getCondition();
                if (constants.getInFact(stmt).get(condition.getOperand1()).isConstant()
                        && constants.getInFact(stmt).get(condition.getOperand2()).isConstant()) {
                    int operand1 = constants.getInFact(stmt).get(condition.getOperand1()).getConstant();
                    int operand2 = constants.getInFact(stmt).get(condition.getOperand2()).getConstant();
                    boolean condition_value = switch (condition.getOperator()) {
                        case NE -> operand1 != operand2;
                        case LT -> operand1 < operand2;
                        case LE -> operand1 <= operand2;
                        case GT -> operand1 > operand2;
                        case GE -> operand1 >= operand2;
                        case EQ -> operand1 == operand2;
                    };
                    cfg.getOutEdgesOf(stmt).forEach(branch -> {
                        if ((branch.getKind() == Edge.Kind.IF_TRUE && condition_value)
                                || (branch.getKind() == Edge.Kind.IF_FALSE && !condition_value)) {
                            if (!visited[branch.getTarget().getIndex()] && !worklist.contains(branch.getTarget())) {
                                worklist.offer(branch.getTarget());
                            }
                        }
                    });
                }
                // unreachable code, switch case
            } else if (stmt instanceof SwitchStmt s) {
                Var condition = s.getVar();
                if (constants.getInFact(stmt).get(condition).isConstant()) {
                    int condition_value = constants.getInFact(stmt).get(condition).getConstant();
                    Stmt match_case = null;
                    Stmt default_case = null;
                    for (Edge<Stmt> branch : cfg.getOutEdgesOf(stmt)) {
                        if (branch.getKind() == Edge.Kind.SWITCH_CASE && branch.getCaseValue() == condition_value) {
                            match_case = branch.getTarget();
                        } else if (branch.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            default_case = branch.getTarget();
                        }
                    }
                    if (match_case != null) {
                        if (!visited[match_case.getIndex()] && !worklist.contains(match_case)) {
                            worklist.offer(match_case);
                        }
                    } else if (default_case != null) {
                        if (!visited[default_case.getIndex()] && !worklist.contains(default_case)) {
                            worklist.offer(default_case);
                        }
                    }
                }
            } else {
                // dead Assignment
                if (stmt instanceof DefinitionStmt<?, ?> d) {
                    if ((d instanceof AssignStmt<?, ?> || (d instanceof Invoke && hasNoSideEffect(d.getRValue())))
                            && d.getLValue() instanceof Var v) {
                        if (!liveVars.getOutFact(stmt).contains(v)) {
                            deadCode.add(stmt);
                        }
                    }
                }
                cfg.getSuccsOf(stmt).forEach(successor -> {
                    if (!visited[successor.getIndex()] && !worklist.contains(successor)) {
                        worklist.offer(successor);
                    }
                });
            }
        }
        cfg.getNodes().forEach(node -> {
            if (!visited[node.getIndex()]) {
                deadCode.add(node);
            }
        });

        System.out.println(deadCode);
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}

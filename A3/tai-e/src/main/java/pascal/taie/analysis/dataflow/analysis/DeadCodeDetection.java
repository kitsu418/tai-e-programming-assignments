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
        // Your task is to recognize dead code in ir and add it to deadCode
        for (Stmt stmt : cfg.getNodes()) {
            System.out.printf("#%d: %s, in: %s, out: %s\n", stmt.getLineNumber(), stmt, liveVars.getInFact(stmt), liveVars.getOutFact(stmt));
        }
        Set<Stmt> visited_node = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Stmt stmt;
        Queue<Stmt> worklist = new LinkedList<>();
        worklist.offer(cfg.getEntry());
        while (!worklist.isEmpty()) {
            stmt = worklist.remove();
            if (!visited_node.add(stmt)) {
                continue;
            }
            // unreachable code, if case
            if (stmt instanceof If s) {
                Value condition = ConstantPropagation.evaluate(s.getCondition(), constants.getInFact(s));
                if (condition.isConstant()) {
                    int condition_value = condition.getConstant();
                    cfg.getOutEdgesOf(stmt).forEach(branch -> {
                        if ((branch.getKind() == Edge.Kind.IF_TRUE && condition_value == 1)
                                || (branch.getKind() == Edge.Kind.IF_FALSE && condition_value == 0)) {
                            worklist.offer(branch.getTarget());
                        }
                    });
                } else {
                    worklist.addAll(cfg.getSuccsOf(stmt));
                }
                // unreachable code, switch case
            } else if (stmt instanceof SwitchStmt s) {
                Value condition = ConstantPropagation.evaluate(s.getVar(), constants.getInFact(s));
                if (condition.isConstant()) {
                    int condition_value = condition.getConstant();
                    Stmt match_case = null;
                    for (Edge<Stmt> branch : cfg.getOutEdgesOf(stmt)) {
                        if (branch.getKind() == Edge.Kind.SWITCH_CASE && branch.getCaseValue() == condition_value) {
                            match_case = branch.getTarget();
                        }
                    }
                    worklist.offer(match_case != null ? match_case : s.getDefaultTarget());
                } else {
                    worklist.addAll(cfg.getSuccsOf(s));
                }
            } else {
                // dead Assignment
                if (stmt instanceof DefinitionStmt<?, ?> d) {
                    if (d instanceof AssignStmt<?, ?> && hasNoSideEffect(d.getRValue())
                            && d.getLValue() instanceof Var v) {
                        if (!liveVars.getResult(stmt).contains(v)) {
                            deadCode.add(stmt);
                        }
                    }
                }
                worklist.addAll(cfg.getSuccsOf(stmt));
            }
        }
        cfg.getNodes().forEach(node -> {
            if (!visited_node.contains(node)) {
                deadCode.add(node);
            }
        });
        deadCode.remove(cfg.getExit());
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

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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.MapFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Map;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> worklist = new LinkedList<Node>(cfg.getNodes());
        Node node;
        if (analysis instanceof ConstantPropagation) {
            CPFact in;
            while (!worklist.isEmpty()) {
                node = worklist.remove();
                System.out.printf("#%s(before): %s, in: %s, out: %s, %s\n", ((Stmt) node).getLineNumber(), node, result.getInFact(node), result.getOutFact(node), ((Stmt) node).getDef().isPresent() ? ((Stmt) node).getDef().get() : null);
                ((CPFact) result.getInFact(node)).clear();
                for (Node predecessor : cfg.getPredsOf(node)) {
                    ((ConstantPropagation) analysis).meetInto((CPFact) result.getOutFact(predecessor), (CPFact) result.getInFact(node));
                }
                if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                    cfg.getSuccsOf(node).forEach(successor -> {
                        if (!worklist.contains(successor)) {
                            worklist.offer(successor);
                        }
                    });
                }
                System.out.printf("#%s(after): %s, in: %s, out: %s, %s\n", ((Stmt) node).getLineNumber(), node, result.getInFact(node), result.getOutFact(node), ((Stmt) node).getDef().isPresent() ? ((Stmt) node).getDef().get() : null);
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}

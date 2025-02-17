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
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;
import java.util.function.Consumer;

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

        Stmt entry = cfg.getEntry();
        Set<Stmt> reachableSet = new HashSet<>();

        Set<Stmt> visitedSet = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();
        queue.offer(entry);
        while (!queue.isEmpty()) {
            Stmt current = queue.poll();
            reachableSet.add(current);
            visitedSet.add(current);
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);

            if (current instanceof If) {
                CPFact cpFact = constants.getResult(current);
                ConditionExp exp = ((If) current).getCondition();
                Value value = ConstantPropagation.evaluate(exp, cpFact);

                boolean isTrueCondition = value.isConstant() && value.getConstant() > 0;
                for (Edge<Stmt> edge : outEdges) {
                    if (edge.getKind() == Edge.Kind.IF_TRUE && isTrueCondition && !visitedSet.contains(edge.getTarget())) {
                        queue.offer(edge.getTarget());
                    }
                    if (edge.getKind() == Edge.Kind.IF_FALSE && !isTrueCondition && !visitedSet.contains(edge.getTarget())) {
                        queue.offer(edge.getTarget());
                    }
                }

            } else if (current instanceof SwitchStmt) {
                Var var = ((SwitchStmt) current).getVar();
                CPFact cpFact = constants.getResult(current);
                Value value = cpFact.get(var);
                if (value != null && value.isConstant()) {
                    int constant = value.getConstant();
                    boolean isMatched = false;
                    boolean isFallThrough = false;
                    Edge<Stmt> switchDefaultEdge = null;
                    for (Edge<Stmt> edge : outEdges) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE) {
                            int caseValue = edge.getCaseValue();
                            if (constant == caseValue) {
                                isMatched = true;
                                if (!visitedSet.contains(edge.getTarget())) {
                                    queue.offer(edge.getTarget());
                                }
                                Stmt target = edge.getTarget();
                                isFallThrough = target.canFallThrough();
                            } else {
                                if (isFallThrough) {
                                    if (!visitedSet.contains(edge.getTarget())) {
                                        queue.offer(edge.getTarget());
                                    }
                                    Stmt target = edge.getTarget();
                                    isFallThrough = target.canFallThrough();
                                }
                            }
                        } else if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            switchDefaultEdge = edge;
                        }
                    }
                    if (!isMatched && switchDefaultEdge != null && !visitedSet.contains(switchDefaultEdge.getTarget())) {
                        queue.offer(switchDefaultEdge.getTarget());
                    }
                } else {
                    for (Edge<Stmt> edge : outEdges) {
                        if (!visitedSet.contains(edge.getTarget())) {
                            queue.offer(edge.getTarget());
                        }
                    }
                }
            } else if (current instanceof AssignStmt) {
                SetFact<Var> result = liveVars.getResult(current);
                Var var = ((AssignStmt<Var, RValue>) current).getLValue();
                RValue rValue = ((AssignStmt<Var, RValue>) current).getRValue();
                if (!result.contains(var) && hasNoSideEffect(rValue)) {
                    deadCode.add(current);
                }
                for (Edge<Stmt> edge : outEdges) {
                    if (!visitedSet.contains(edge.getTarget())) {
                        queue.offer(edge.getTarget());
                    }
                }
            } else {
                for (Edge<Stmt> edge : outEdges) {
                    if (!visitedSet.contains(edge.getTarget())) {
                        queue.offer(edge.getTarget());
                    }
                }
            }
        }

        for (Stmt stmt : cfg) {
            if (!reachableSet.contains(stmt) && !cfg.isExit(stmt)) {
                deadCode.add(stmt);
            }
        }

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    private static Set<Stmt> findDeadAssignment(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        Set<Stmt> deadAssignmentSet = new HashSet<>();
        Stmt entry = cfg.getEntry();
        Queue<Stmt> queue = new LinkedList<>();
        queue.offer(entry);
        cfg.forEach(queue::offer);
        while (!queue.isEmpty()) {
            Stmt current = queue.poll();
            System.out.println("current:" + current.toString());
            if (current instanceof AssignStmt) {
                SetFact<Var> result = liveVars.getResult(current);
                Var var = ((AssignStmt<Var, RValue>) current).getLValue();
                RValue rValue = ((AssignStmt<Var, RValue>) current).getRValue();
                if (!result.contains(var) && hasNoSideEffect(rValue)) {
                    deadAssignmentSet.add(current);
                }
            }
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);
            for (Edge<Stmt> edge : outEdges) {
                queue.offer(edge.getTarget());
            }
        }
        return deadAssignmentSet;
    }

    private static Set<Stmt> findUnreachableBranch(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        Set<Stmt> reachableSet = new HashSet<>();

        Stmt entry = cfg.getEntry();
        Queue<Stmt> queue = new LinkedList<>();
        queue.offer(entry);
        while (!queue.isEmpty()) {
            Stmt current = queue.poll();
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);
            reachableSet.add(current);

        }

        Set<Stmt> unreachableSet = new HashSet<>();
        for (Stmt stmt : cfg) {
            if (!reachableSet.contains(stmt)) {
                unreachableSet.add(stmt);
            }
        }
        return unreachableSet;
    }

    private static Set<Stmt> findControlFlowUnreachable(CFG<Stmt> cfg) {
        Stmt entry = cfg.getEntry();
        Set<Stmt> reachableSet = new HashSet<>();

        Queue<Stmt> queue = new LinkedList<>();
        queue.offer(entry);
        while (!queue.isEmpty()) {
            Stmt current = queue.poll();
            reachableSet.add(current);
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);
            for (Edge<Stmt> edge : outEdges) {
                queue.offer(edge.getTarget());
            }
        }

        Set<Stmt> unreachableSet = new HashSet<>();
        for (Stmt stmt : cfg) {
            if (!reachableSet.contains(stmt)) {
                unreachableSet.add(stmt);
            }
        }
        return unreachableSet;
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

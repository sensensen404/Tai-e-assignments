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
import pascal.taie.util.collection.Pair;

import java.util.*;

import static pascal.taie.analysis.graph.cfg.Edge.Kind.IF_FALSE;
import static pascal.taie.analysis.graph.cfg.Edge.Kind.IF_TRUE;

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
            Stmt stmt = queue.poll();
            if (!visitedSet.add(stmt)) {
                continue;
            }

            reachableSet.add(stmt);
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(stmt);

            // 处理无用赋值
            if (stmt instanceof AssignStmt && isDeadAssignment(stmt, liveVars)) {
                deadCode.add(stmt);
            }

            // 找到控制流的下一条语句
            Stmt followingStmt = getFollowingControlStmt(stmt, constants, outEdges);
            if (followingStmt == null) {
                outEdges.forEach(edge -> queue.offer(edge.getTarget()));
            } else {
                queue.offer(followingStmt);
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

    private static Stmt getFollowingControlStmt(Stmt stmt, DataflowResult<Stmt, CPFact> constants, Set<Edge<Stmt>> outEdges) {
        Stmt followingStmt = null;
        if (stmt instanceof If) {
            followingStmt = getFollowingIfStmt((If) stmt, constants, outEdges);
        }
        if (stmt instanceof SwitchStmt) {
            followingStmt = getFollowingSwitchStmt((SwitchStmt) stmt, constants);
        }
        return followingStmt;
    }


    private static boolean isDeadAssignment(Stmt stmt, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        AssignStmt<Var, RValue> assignStmt = ((AssignStmt<Var, RValue>) stmt);
        SetFact<Var> result = liveVars.getResult(stmt);
        Var var = assignStmt.getLValue();
        RValue rValue = assignStmt.getRValue();
        return !result.contains(var) && hasNoSideEffect(rValue);
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

    private static Stmt getFollowingIfStmt(If ifStmt, DataflowResult<Stmt, CPFact> constants, Set<Edge<Stmt>> outEdges) {
        CPFact cpFact = constants.getResult(ifStmt);
        ConditionExp exp = ifStmt.getCondition();
        Value value = ConstantPropagation.evaluate(exp, cpFact);
        if (!value.isConstant()) {
            return null;
        }

        int constant = value.getConstant();
        Edge.Kind kind = constant == 1 ? IF_TRUE : IF_FALSE;
        return outEdges.stream()
                .filter(edge -> edge.getKind() == kind)
                .map(Edge::getTarget)
                .findFirst()
                .orElse(null);
    }

    private static Stmt getFollowingSwitchStmt(SwitchStmt switchStmt, DataflowResult<Stmt, CPFact> constants) {
        Var var = switchStmt.getVar();
        CPFact cpFact = constants.getResult(switchStmt);
        Value value = ConstantPropagation.evaluate(var, cpFact);
        if (!value.isConstant()) {
            return null;
        }

        int constant = value.getConstant();
        Stmt defaultTarget = switchStmt.getDefaultTarget();
        return switchStmt.getCaseTargets().stream()
                .filter(pair -> constant == pair.first())
                .map(Pair::second)
                .findFirst()
                .orElse(defaultTarget);
    }
}

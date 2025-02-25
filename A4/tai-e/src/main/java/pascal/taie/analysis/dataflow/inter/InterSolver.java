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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.IR;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        for (Node node : icfg) {
            boolean isEntry = icfg.entryMethods().anyMatch(m -> {
                Node entryNode = icfg.getEntryOf(m);
                return entryNode == node;
            });
            if (isEntry) {
                result.setInFact(node, analysis.newBoundaryFact(node));
                result.setOutFact(node, analysis.newInitialFact());
            } else {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    private void doSolve() {
        // TODO - finish me
        workList = new LinkedList<>(icfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.poll();

            Fact infact = analysis.newInitialFact();
//            Fact infact = result.getInFact(node);
            Set<ICFGEdge<Node>> inEdges = icfg.getInEdgesOf(node);

            for (ICFGEdge<Node> edge : inEdges) {
                Node source = edge.getSource();
                Fact sourceOutFact = result.getOutFact(source);
                Fact transferredOutfact = analysis.transferEdge(edge, sourceOutFact);
                analysis.meetInto(transferredOutfact, infact);
            }

            Fact outfact = result.getOutFact(node);
            if (analysis.transferNode(node, infact, outfact)) {
                Set<Node> succs = icfg.getSuccsOf(node);
                succs.forEach(workList::offer);
            }

        }
    }
}

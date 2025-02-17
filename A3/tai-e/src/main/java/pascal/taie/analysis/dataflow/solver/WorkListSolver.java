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
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> queue = new LinkedList<>(cfg.getNodes());
        while (!queue.isEmpty()) {
            Node node = queue.poll();
            Set<Node> preds = cfg.getPredsOf(node);

            Fact infact = result.getInFact(node);
            for (Node pred : preds) {
                Fact outfactOfPred = result.getOutFact(pred);
                analysis.meetInto(outfactOfPred, infact);
            }

            Fact outfact = result.getOutFact(node);
            if (analysis.transferNode(node, infact, outfact)) {
                Set<Node> succs = cfg.getSuccsOf(node);
                succs.forEach(queue::offer);
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
//        Queue<Node> queue = new LinkedList<>(cfg.getNodes());
//        while (!queue.isEmpty()) {
//            Node node = queue.poll();
//            Set<Node> succs = cfg.getSuccsOf(node);
//
//            Fact outfact = result.getOutFact(node);
//            for (Node succ : succs) {
//                Fact infactOfSucc = result.getInFact(succ);
//                analysis.meetInto(infactOfSucc, outfact);
//            }
//
//            Fact infact = result.getInFact(node);
//            if (analysis.transferNode(node, infact, outfact)) {
//                Set<Node> preds = cfg.getPredsOf(node);
//                preds.forEach(queue::offer);
//            }
//        }

        boolean changed = true;
        while(changed) {
            changed = false;
            for (Node node: cfg) {
                if (cfg.isExit(node)) {
                    continue;
                }

                Fact outfact = result.getOutFact(node);
                for (Node succ: cfg.getSuccsOf(node)) {
                    Fact inFactOfSucc = result.getInFact(succ);
                    analysis.meetInto(inFactOfSucc, outfact);
                }

                Fact inFact = result.getInFact(node);
                if (analysis.transferNode(node, inFact, outfact)) {
                    changed = true;
                }
            }
        }
    }
}

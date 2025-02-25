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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> queue = new LinkedList<>();
        queue.offer(entry);
        while (!queue.isEmpty()) {
            JMethod method = queue.poll();
            if (callGraph.contains(method)) {
                continue;
            }
            callGraph.addReachableMethod(method);
            Set<Invoke> callsites = callGraph.getCallSitesIn(method);
            for (Invoke invoke : callsites) {
                Set<JMethod> calltargets = resolve(invoke);
                for (JMethod target : calltargets) {
                    callGraph.addEdge(new Edge<>(CallKind.VIRTUAL, invoke, target));
                    queue.offer(target);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> targets = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        JClass jclass = methodRef.getDeclaringClass();

        if (callSite.isStatic()) {
            JMethod jmethod = jclass.getDeclaredMethod(subsignature);
            targets.add(jmethod);
        }

        if (callSite.isSpecial()) {
            JMethod jmethod = dispatch(jclass, subsignature);
            targets.add(jmethod);
        }
        if (callSite.isVirtual() || callSite.isInterface()) {

            List<JClass> jclassList = getAllSubclassesOf(jclass);
            jclassList.add(jclass);
            for (JClass subclass : jclassList) {
                JMethod jmethodSubclass = dispatch(subclass, subsignature);
                if (jmethodSubclass != null) {
                    targets.add(jmethodSubclass);
                }
            }
        }
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null && !jMethod.isAbstract()) {
            return jMethod;
        }
        JClass superClass = jclass.getSuperClass();
        if (superClass == null) {
            return null;
        }
        return dispatch(superClass, subsignature);
    }

    private List<JClass> getAllSubclassesOf(JClass jclass) {
        List<JClass> result = new ArrayList<>();
        Collection<JClass> directSubclasses = hierarchy.getDirectSubclassesOf(jclass);
        for (JClass item : directSubclasses) {
            result.add(item);
            result.addAll(getAllSubclassesOf(item));
        }
        Collection<JClass> directImplementors = hierarchy.getDirectImplementorsOf(jclass);
        for (JClass item : directImplementors) {
            result.add(item);
            result.addAll(getAllSubclassesOf(item));
        }
        Collection<JClass> directSubinterfaces = hierarchy.getDirectSubinterfacesOf(jclass);
        for (JClass item : directSubinterfaces) {
            result.add(item);
            result.addAll(getAllSubclassesOf(item));
        }

        return result;
    }
}

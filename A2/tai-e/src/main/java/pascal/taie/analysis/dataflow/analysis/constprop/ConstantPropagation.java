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
import soot.JastAddJ.ArithmeticExpr;

import java.util.List;
import java.util.function.BiConsumer;

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
        CPFact cpFact = new CPFact();
        List<Var> varList = cfg.getIR().getParams();
        for (Var var : varList) {
            cpFact.update(var, Value.getNAC());
        }
        return cpFact;
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
            Value targetValue = target.get(var);
            Value newValue = meetValue(value, targetValue);
            target.update(var, newValue);
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        }
        if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        }
        if (v1.getConstant() == v2.getConstant()) {
            return Value.makeConstant(v1.getConstant());
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        out.copyFrom(in);
        if (stmt instanceof DefinitionStmt) {
            Var lValue = ((DefinitionStmt<Var, RValue>) stmt).getLValue();
            RValue rValue = ((DefinitionStmt<Var, RValue>) stmt).getRValue();

            out.remove(lValue);
            Value value = evaluate(rValue, in);
            if (lValue != null && value != null) {
                out.update(lValue, value);
            }
        }
        return false;
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
        if (exp instanceof IntLiteral) {
            int constant = ((IntLiteral) exp).getValue();
            return Value.makeConstant(constant);
        } else if (exp instanceof Var) {
            if (canHoldInt((Var) exp)) {
                Value value = in.get((Var) exp);
                if (value.isConstant()) {
                    return Value.makeConstant(value.getConstant());
                } else {
                    return value;
                }
            }
        } else if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            BinaryExp.Op operator = ((BinaryExp) exp).getOperator();

            if (!canHoldInt(operand1) || !canHoldInt(operand2)) {
                return Value.getNAC();
            }

            Value operandValue1 = in.get(operand1);
            Value operandValue2 = in.get(operand2);

            if (!operandValue1.isConstant() || !operandValue2.isConstant()) {
                return Value.getNAC();
            }
            int value1 = operandValue1.getConstant();
            int value2 = operandValue2.getConstant();

            Value result = null;
            if (exp instanceof ArithmeticExp) {
                if (operator == ArithmeticExp.Op.ADD) {
                    result = Value.makeConstant(value1 + value2);
                } else if (operator == ArithmeticExp.Op.SUB) {
                    result = Value.makeConstant(value1 - value2);
                } else if (operator == ArithmeticExp.Op.MUL) {
                    result = Value.makeConstant(value1 * value2);
                } else if (operator == ArithmeticExp.Op.DIV) {
                    if (value2 == 0) {
                        result = Value.getUndef();
                    } else {
                        result = Value.makeConstant(value1 / value2);
                    }
                } else if (operator == ArithmeticExp.Op.REM) {
                    if (value2 == 0) {
                        result = Value.getUndef();
                    } else {
                        result = Value.makeConstant(value1 % value2);
                    }
                }
            } else if (exp instanceof BitwiseExp) {
                if (operator == BitwiseExp.Op.OR) {
                    result = Value.makeConstant(value1 | value2);
                } else if (operator == BitwiseExp.Op.AND) {
                    result = Value.makeConstant(value1 & value2);
                } else if (operator == BitwiseExp.Op.XOR) {
                    result = Value.makeConstant(value1 ^ value2);
                }
            } else if (exp instanceof ConditionExp) {
                if (operator == ConditionExp.Op.EQ) {
                    result = Value.makeConstant(value1 == value2 ? 1 : 0);
                } else if (operator == ConditionExp.Op.NE) {
                    result = Value.makeConstant(value1 != value2 ? 1 : 0);
                } else if (operator == ConditionExp.Op.LT) {
                    result = Value.makeConstant(value1 < value2 ? 1 : 0);
                } else if (operator == ConditionExp.Op.GT) {
                    result = Value.makeConstant(value1 > value2 ? 1 : 0);
                } else if (operator == ConditionExp.Op.LE) {
                    result = Value.makeConstant(value1 <= value2 ? 1 : 0);
                } else if (operator == ConditionExp.Op.GE) {
                    result = Value.makeConstant(value1 >= value2 ? 1 : 0);
                }
            } else if (exp instanceof ShiftExp) {
                if (operator == ShiftExp.Op.SHL) {
                    result = Value.makeConstant(value1 << value2);
                } else if (operator == ShiftExp.Op.SHR) {
                    result = Value.makeConstant(value1 >> value2);
                } else if (operator == ShiftExp.Op.USHR) {
                    result = Value.makeConstant(value1 >>> value2);
                }
            } else {
                result = Value.getNAC();
            }
            return result;
        } else {
            return Value.getNAC();
        }
        return null;
    }
}

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

import java.util.List;

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
            if (canHoldInt(var)) {
                cpFact.update(var, Value.getNAC());
            }
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
        CPFact copy = in.copy();
        if (stmt instanceof DefinitionStmt) {
            Var lValue = ((DefinitionStmt<Var, RValue>) stmt).getLValue();
            if (lValue != null && canHoldInt(lValue)) {
                RValue rValue = ((DefinitionStmt<Var, RValue>) stmt).getRValue();
                Value value = evaluate(rValue, copy);
                copy.update(lValue, value);
            }
        }
        return out.copyFrom(copy);
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
            int value = ((IntLiteral) exp).getValue();
            return Value.makeConstant(value);
        } else if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            BinaryExp.Op operator = ((BinaryExp) exp).getOperator();
            if (!canHoldInt(operand1) || !canHoldInt(operand2)) {
                return Value.getNAC();
            }

            Value value1 = in.get(operand1);
            Value value2 = in.get(operand2);
            if (!value1.isConstant() || !value2.isConstant()) {
                return Value.getNAC();
            }

            int constant1 = value1.getConstant();
            int constant2 = value2.getConstant();

            Value result;
            if (exp instanceof ArithmeticExp) {
                result = evaluateArithmetic(operator, constant1, constant2);
            } else if (exp instanceof BitwiseExp) {
                result = evaluateBitwise(operator, constant1, constant2);
            } else if (exp instanceof ConditionExp) {
                result = evaluateCondition(operator, constant1, constant2);
            } else if (exp instanceof ShiftExp) {
                result = evaluateShift(operator, constant1, constant2);
            } else {
                result = Value.getNAC();
            }
            return result;
        } else {
            return Value.getNAC();
        }
    }

    private static Value evaluateShift(BinaryExp.Op operator, int value1, int value2) {
        return switch ((ShiftExp.Op) operator) {
            case SHL ->  Value.makeConstant(value1 << value2);
            case SHR -> Value.makeConstant(value1 >> value2);
            case USHR -> Value.makeConstant(value1 >>> value2);
        };
    }

    private static Value evaluateCondition(BinaryExp.Op operator, int value1, int value2) {
        return switch ((ConditionExp.Op) operator) {
            case EQ -> Value.makeConstant(value1 == value2 ? 1 : 0);
            case NE ->  Value.makeConstant(value1 != value2 ? 1 : 0);
            case LT -> Value.makeConstant(value1 < value2 ? 1 : 0);
            case GT -> Value.makeConstant(value1 > value2 ? 1 : 0);
            case LE -> Value.makeConstant(value1 <= value2 ? 1 : 0);
            case GE -> Value.makeConstant(value1 >= value2 ? 1 : 0);
        };
    }

    private static Value evaluateBitwise(BinaryExp.Op operator, int value1, int value2) {
        return switch ((BitwiseExp.Op) operator) {
            case OR -> Value.makeConstant(value1 | value2);
            case AND -> Value.makeConstant(value1 & value2);
            case XOR -> Value.makeConstant(value1 ^ value2);
        };
    }

    private static Value evaluateArithmetic(BinaryExp.Op operator, int value1, int value2) {
        if ((operator == ArithmeticExp.Op.DIV || operator == ArithmeticExp.Op.REM) && value2 == 0) {
            return Value.getUndef();
        }
        return switch ((ArithmeticExp.Op) operator) {
            case ADD -> Value.makeConstant(value1 + value2);
            case SUB -> Value.makeConstant(value1 - value2);
            case MUL -> Value.makeConstant(value1 * value2);
            case DIV -> Value.makeConstant(value1 / value2);
            case REM -> Value.makeConstant(value1 % value2);
        };
    }
}

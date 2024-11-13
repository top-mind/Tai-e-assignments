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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;


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

        CPFact fact = new CPFact();

        for (Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(target.get(var), fact.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        if (v1.isUndef())
            return v2;
        if (v2.isUndef())
            return v1;
        if (v1.equals(v2))
            return v1;
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            LValue lValue = definitionStmt.getLValue();
            if (lValue instanceof Var gen && canHoldInt(gen)) {
                Value result = evaluate(definitionStmt.getRValue(), in);
                CPFact newFact = in.copy();
                newFact.update(gen, result);
                return out.copyFrom(newFact);
            }
        }
        return out.copyFrom(in);
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
        if (exp instanceof Var var) {
            return in.get(var);
        }
        if (exp instanceof IntLiteral literal) {
            return Value.makeConstant(literal.getValue());
        }
        if (exp instanceof BinaryExp binary) {
            Value v1 = in.get(binary.getOperand1());
            Value v2 = in.get(binary.getOperand2());

            // corner: anything / or % 0 is UNDEF
            if ((binary.getOperator() == ArithmeticExp.Op.DIV ||
                    binary.getOperator() == ArithmeticExp.Op.REM) &&
                    v2.isConstant() && v2.getConstant() == 0)
                return Value.getUndef();
            if (v1.isNAC() || v2.isNAC())
                return Value.getNAC();
            if (v1.isConstant() && v2.isConstant()) {
                return evaluateBinaryConstant(binary.getOperator(), v1.getConstant(), v2.getConstant());
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }

    public static Value evaluateBinaryConstant(BinaryExp.Op rawOp, int v1, int v2) {
        if (rawOp instanceof ArithmeticExp.Op op) {
            return switch (op) {
                case ADD -> Value.makeConstant(v1 + v2);
                case SUB -> Value.makeConstant(v1 - v2);
                case MUL -> Value.makeConstant(v1 * v2);
                case DIV -> Value.makeConstant(v1 / v2);
                case REM -> Value.makeConstant(v1 % v2);
            };
        }
        if (rawOp instanceof ConditionExp.Op op) {
            return switch (op) {
                case EQ -> Value.makeConstant(v1 == v2 ? 1 : 0);
                case NE -> Value.makeConstant(v1 != v2 ? 1 : 0);
                case GE -> Value.makeConstant(v1 >= v2 ? 1 : 0);
                case LE -> Value.makeConstant(v1 <= v2 ? 1 : 0);
                case GT -> Value.makeConstant(v1 > v2 ? 1 : 0);
                case LT -> Value.makeConstant(v1 < v2 ? 1 : 0);
            };
        }
        if (rawOp instanceof ShiftExp.Op op) {
            return switch (op) {
                case SHL -> Value.makeConstant(v1 << v2);
                case SHR -> Value.makeConstant(v1 >> v2);
                case USHR -> Value.makeConstant(v1 >>> v2);
            };
        }
        if (rawOp instanceof BitwiseExp.Op op) {
            return switch (op) {
                case AND -> Value.makeConstant(v1 & v2);
                case OR -> Value.makeConstant(v1 | v2);
                case XOR -> Value.makeConstant(v1 ^ v2);
            };
        }
        // throw new AnalysisException("unexpected operator: " + rawOp);
        return Value.getNAC();
    }
}

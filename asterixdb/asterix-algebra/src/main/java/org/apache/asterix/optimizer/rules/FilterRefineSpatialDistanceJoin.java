/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package org.apache.asterix.optimizer.rules;

import com.esri.core.geometry.Geometry;
import org.apache.asterix.om.base.AInt64;
import org.apache.asterix.om.constants.AsterixConstantValue;
import org.apache.asterix.om.functions.BuiltinFunctions;
import org.apache.commons.lang3.mutable.Mutable;
import org.apache.commons.lang3.mutable.MutableObject;
import org.apache.hyracks.algebricks.common.exceptions.AlgebricksException;
import org.apache.hyracks.algebricks.core.algebra.base.*;
import org.apache.hyracks.algebricks.core.algebra.expressions.*;
import org.apache.hyracks.algebricks.core.algebra.operators.logical.AbstractBinaryJoinOperator;
import org.apache.hyracks.algebricks.core.algebra.operators.logical.AbstractLogicalOperator;
import org.apache.hyracks.algebricks.core.rewriter.base.IAlgebraicRewriteRule;
import org.apache.hyracks.api.constraints.expressions.ConstraintExpression;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.List;

public class FilterRefineSpatialDistanceJoin implements IAlgebraicRewriteRule {

    private static final Logger LOGGER = LogManager.getLogger();
    private static final int LEFT = 0;
    private static final int RIGHT = 1;

    @Override
    public boolean rewritePre(Mutable<ILogicalOperator> opRef, IOptimizationContext context)
            throws AlgebricksException {
        return false;
    }

    @Override
    public boolean rewritePost(Mutable<ILogicalOperator> opRef, IOptimizationContext context)
            throws AlgebricksException {
        // Current operator should be a join.
        AbstractLogicalOperator op = (AbstractLogicalOperator) opRef.getValue();
        if (op.getOperatorTag() != LogicalOperatorTag.INNERJOIN
                && op.getOperatorTag() != LogicalOperatorTag.LEFTOUTERJOIN) {
            return false;
        }

        // Finds ST_INTERSECTS function in the join condition.
        AbstractBinaryJoinOperator joinOp = (AbstractBinaryJoinOperator) op;
        Mutable<ILogicalExpression> joinConditionRef = joinOp.getCondition();
        ILogicalExpression joinCondition = joinConditionRef.getValue();

        if (joinCondition.getExpressionTag() != LogicalExpressionTag.FUNCTION_CALL) {
            return false;
        }

        AbstractFunctionCallExpression funcExpr = (AbstractFunctionCallExpression) joinCondition;
        if (BuiltinFunctions.LT.equals(funcExpr.getFunctionIdentifier())) {

        }
        if (!(
                funcExpr.getFunctionIdentifier().equals(BuiltinFunctions.LT) ||
                        funcExpr.getFunctionIdentifier().equals(BuiltinFunctions.LE) ||
                        funcExpr.getFunctionIdentifier().equals(BuiltinFunctions.GT) ||
                        funcExpr.getFunctionIdentifier().equals(BuiltinFunctions.GE) ||
                        funcExpr.getFunctionIdentifier().equals(BuiltinFunctions.NEQ)
        )
        ) {
            return false;
        }

        // Extracts ST_INTERSECTS function's arguments
        List<Mutable<ILogicalExpression>> inputExprs = funcExpr.getArguments();
        if (inputExprs.size() != 2) {
            return false;
        }

        ILogicalExpression leftOperatingExpr = inputExprs.get(LEFT).getValue();
        ILogicalExpression rightOperatingExpr = inputExprs.get(RIGHT).getValue();


        if(!(((ScalarFunctionCallExpression) leftOperatingExpr).getFunctionIdentifier().equals(BuiltinFunctions.ST_DISTANCE)))
        {
            return false;
        }


        LOGGER.info("st_distance is called");

        LogicalVariable inputVar0;
        LogicalVariable inputVar1;
        IAlgebricksConstantValue inputVar2;

        inputVar0 = ((VariableReferenceExpression) ((ScalarFunctionCallExpression) leftOperatingExpr).getArguments().get(LEFT).getValue()).getVariableReference();
        inputVar1 = ((VariableReferenceExpression) ((ScalarFunctionCallExpression) leftOperatingExpr).getArguments().get(RIGHT).getValue()).getVariableReference();
        inputVar2 = ((ConstantExpression) rightOperatingExpr).getValue();

        ScalarFunctionCallExpression leftOffset =
                new ScalarFunctionCallExpression(BuiltinFunctions.getBuiltinFunctionInfo(BuiltinFunctions.ST_MBR_OFFSET),
                        new MutableObject<>(new VariableReferenceExpression(inputVar0)),
                        new MutableObject<>(new ConstantExpression(inputVar2)));

        ScalarFunctionCallExpression rightOffset =
                new ScalarFunctionCallExpression(BuiltinFunctions.getBuiltinFunctionInfo(BuiltinFunctions.ST_MBR_OFFSET),
                        new MutableObject<>(new VariableReferenceExpression(inputVar1)),
                        new MutableObject<>(new ConstantExpression(inputVar2)));

        ScalarFunctionCallExpression left =
                new ScalarFunctionCallExpression(BuiltinFunctions.getBuiltinFunctionInfo(BuiltinFunctions.ST_MBR),
                        new MutableObject<>(leftOffset));

        ScalarFunctionCallExpression right =
                new ScalarFunctionCallExpression(BuiltinFunctions.getBuiltinFunctionInfo(BuiltinFunctions.ST_MBR),
                        new MutableObject<>(rightOffset));

        ScalarFunctionCallExpression spatialIntersect = new ScalarFunctionCallExpression(
                BuiltinFunctions.getBuiltinFunctionInfo(BuiltinFunctions.SPATIAL_INTERSECT), new MutableObject<>(left),
                new MutableObject<>(right));

        ScalarFunctionCallExpression stFunc = new ScalarFunctionCallExpression(
                BuiltinFunctions.getBuiltinFunctionInfo(BuiltinFunctions.ST_DISTANCE),
                new MutableObject<>(new VariableReferenceExpression(inputVar0)),
                new MutableObject<>(new VariableReferenceExpression(inputVar1)));

        ScalarFunctionCallExpression comparisonExp = new ScalarFunctionCallExpression(
                BuiltinFunctions.getBuiltinFunctionInfo(funcExpr.getFunctionIdentifier()),
                new MutableObject<>(stFunc),
                new MutableObject<>(new ConstantExpression(inputVar2)));

        ScalarFunctionCallExpression updatedJoinCondition =
                new ScalarFunctionCallExpression(BuiltinFunctions.getBuiltinFunctionInfo(BuiltinFunctions.AND),
                        new MutableObject<>(spatialIntersect), new MutableObject<>(comparisonExp));

        joinConditionRef.setValue(updatedJoinCondition);

        return true;
    }

}

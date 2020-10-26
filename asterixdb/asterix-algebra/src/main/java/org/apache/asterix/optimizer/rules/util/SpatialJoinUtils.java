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

package org.apache.asterix.optimizer.rules.util;

import org.apache.asterix.om.functions.BuiltinFunctions;
import org.apache.hyracks.algebricks.core.algebra.base.ILogicalExpression;
import org.apache.hyracks.algebricks.core.algebra.base.LogicalExpressionTag;
import org.apache.hyracks.algebricks.core.algebra.base.LogicalVariable;
import org.apache.hyracks.algebricks.core.algebra.expressions.AbstractFunctionCallExpression;
import org.apache.hyracks.algebricks.core.algebra.functions.FunctionIdentifier;

import java.util.Collection;

public class SpatialJoinUtils {

    protected static FunctionIdentifier isSpatialJoinCondition(ILogicalExpression e,
                                                               Collection<LogicalVariable> inLeftAll, Collection<LogicalVariable> inRightAll,
                                                               Collection<LogicalVariable> outLeftFields, Collection<LogicalVariable> outRightFields, int left,
                                                               int right) {
        FunctionIdentifier fiReturn;
        if (e.getExpressionTag() != LogicalExpressionTag.FUNCTION_CALL) {
            return null;
        }
        AbstractFunctionCallExpression funcExpr = (AbstractFunctionCallExpression) e;
        FunctionIdentifier fi = funcExpr.getFunctionIdentifier();
        if (BuiltinFunctions.isSpatialFilterFunction(fi)) {
            fiReturn = fi;
        } else {
            return null;
        }

        return fiReturn;
    }
}

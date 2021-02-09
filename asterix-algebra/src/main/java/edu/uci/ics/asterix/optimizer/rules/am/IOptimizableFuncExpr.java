/*
 * Copyright 2009-2013 by The Regents of the University of California
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * you may obtain a copy of the License from
 * 
 *     http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package edu.uci.ics.asterix.optimizer.rules.am;

import edu.uci.ics.asterix.om.types.ATypeTag;
import edu.uci.ics.hyracks.algebricks.core.algebra.base.LogicalVariable;
import edu.uci.ics.hyracks.algebricks.core.algebra.expressions.AbstractFunctionCallExpression;
import edu.uci.ics.hyracks.algebricks.core.algebra.expressions.IAlgebricksConstantValue;

/**
 * Describes a function expression that is optimizable by an access method.
 * Provides convenient methods for accessing arguments (constants, variables)
 * and metadata of such a function.
 */
public interface IOptimizableFuncExpr {
    public AbstractFunctionCallExpression getFuncExpr();

    public int getNumLogicalVars();

    public int getNumConstantVals();

    public LogicalVariable getLogicalVar(int index);

    public void setFieldName(int index, String fieldName);

    public String getFieldName(int index);

    public void setOptimizableSubTree(int index, OptimizableOperatorSubTree subTree);

    public OptimizableOperatorSubTree getOperatorSubTree(int index);

    public IAlgebricksConstantValue getConstantVal(int index);

    public int findLogicalVar(LogicalVariable var);

    public int findFieldName(String fieldName);

    public void substituteVar(LogicalVariable original, LogicalVariable substitution);

    public void setPartialField(boolean partialField);

    public boolean containsPartialField();

    public void setTypeTag(int index, ATypeTag typeTag);

    public ATypeTag getTypeTag(int index);
}

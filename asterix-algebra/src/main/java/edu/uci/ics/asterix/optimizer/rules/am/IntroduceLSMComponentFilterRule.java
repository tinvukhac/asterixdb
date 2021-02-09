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

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.lang3.mutable.Mutable;
import org.apache.commons.lang3.mutable.MutableObject;

import edu.uci.ics.asterix.common.config.DatasetConfig.DatasetType;
import edu.uci.ics.asterix.metadata.declared.AqlDataSource;
import edu.uci.ics.asterix.metadata.declared.AqlMetadataProvider;
import edu.uci.ics.asterix.metadata.declared.DatasetDataSource;
import edu.uci.ics.asterix.metadata.entities.Dataset;
import edu.uci.ics.asterix.metadata.entities.Index;
import edu.uci.ics.asterix.metadata.utils.DatasetUtils;
import edu.uci.ics.asterix.om.base.AInt32;
import edu.uci.ics.asterix.om.base.AString;
import edu.uci.ics.asterix.om.constants.AsterixConstantValue;
import edu.uci.ics.asterix.om.functions.AsterixBuiltinFunctions;
import edu.uci.ics.asterix.om.types.ARecordType;
import edu.uci.ics.asterix.om.types.ATypeTag;
import edu.uci.ics.asterix.om.types.IAType;
import edu.uci.ics.hyracks.algebricks.common.exceptions.AlgebricksException;
import edu.uci.ics.hyracks.algebricks.core.algebra.base.ILogicalExpression;
import edu.uci.ics.hyracks.algebricks.core.algebra.base.ILogicalOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.base.IOptimizationContext;
import edu.uci.ics.hyracks.algebricks.core.algebra.base.LogicalExpressionTag;
import edu.uci.ics.hyracks.algebricks.core.algebra.base.LogicalOperatorTag;
import edu.uci.ics.hyracks.algebricks.core.algebra.base.LogicalVariable;
import edu.uci.ics.hyracks.algebricks.core.algebra.expressions.AbstractFunctionCallExpression;
import edu.uci.ics.hyracks.algebricks.core.algebra.expressions.AbstractLogicalExpression;
import edu.uci.ics.hyracks.algebricks.core.algebra.expressions.ConstantExpression;
import edu.uci.ics.hyracks.algebricks.core.algebra.expressions.VariableReferenceExpression;
import edu.uci.ics.hyracks.algebricks.core.algebra.functions.AlgebricksBuiltinFunctions;
import edu.uci.ics.hyracks.algebricks.core.algebra.functions.AlgebricksBuiltinFunctions.ComparisonKind;
import edu.uci.ics.hyracks.algebricks.core.algebra.functions.FunctionIdentifier;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.AbstractLogicalOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.AssignOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.DataSourceScanOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.SelectOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.UnnestMapOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.util.OperatorPropertiesUtil;
import edu.uci.ics.hyracks.algebricks.core.rewriter.base.IAlgebraicRewriteRule;

public class IntroduceLSMComponentFilterRule implements IAlgebraicRewriteRule {

    @Override
    public boolean rewritePre(Mutable<ILogicalOperator> opRef, IOptimizationContext context) throws AlgebricksException {
        return false;
    }

    @Override
    public boolean rewritePost(Mutable<ILogicalOperator> opRef, IOptimizationContext context)
            throws AlgebricksException {

        if (!checkIfRuleIsApplicable(opRef, context)) {
            return false;
        }

        AbstractLogicalOperator op = (AbstractLogicalOperator) opRef.getValue();
        ILogicalExpression condExpr = ((SelectOperator) op).getCondition().getValue();
        AccessMethodAnalysisContext analysisCtx = analyzeCondition(condExpr);
        if (analysisCtx.matchedFuncExprs.isEmpty()) {
            return false;
        }

        Dataset dataset = getDataset(op, context);
        String filterFieldName = null;
        ARecordType recType = null;
        if (dataset != null && dataset.getDatasetType() == DatasetType.INTERNAL) {
            filterFieldName = DatasetUtils.getFilterField(dataset);
            IAType itemType = ((AqlMetadataProvider) context.getMetadataProvider()).findType(
                    dataset.getDataverseName(), dataset.getItemTypeName());
            if (itemType.getTypeTag() == ATypeTag.RECORD) {
                recType = (ARecordType) itemType;
            }
        }
        if (filterFieldName == null || recType == null) {
            return false;
        }
        List<Index> datasetIndexes = ((AqlMetadataProvider) context.getMetadataProvider()).getDatasetIndexes(
                dataset.getDataverseName(), dataset.getDatasetName());

        List<IOptimizableFuncExpr> optFuncExprs = new ArrayList<IOptimizableFuncExpr>();

        for (int i = 0; i < analysisCtx.matchedFuncExprs.size(); i++) {
            IOptimizableFuncExpr optFuncExpr = analysisCtx.matchedFuncExprs.get(i);
            boolean found = findMacthedExprFieldName(optFuncExpr, op, dataset, recType, datasetIndexes);
            if (found && optFuncExpr.getFieldName(0).compareTo(filterFieldName) == 0) {
                optFuncExprs.add(optFuncExpr);
            }
        }
        if (optFuncExprs.isEmpty()) {
            return false;
        }
        changePlan(optFuncExprs, op, dataset, context);

        OperatorPropertiesUtil.typeOpRec(opRef, context);
        context.addToDontApplySet(this, op);
        return true;
    }

    private AssignOperator createAssignOperator(List<IOptimizableFuncExpr> optFuncExprs,
            List<LogicalVariable> minFilterVars, List<LogicalVariable> maxFilterVars, IOptimizationContext context) {
        List<LogicalVariable> assignKeyVarList = new ArrayList<LogicalVariable>();
        List<Mutable<ILogicalExpression>> assignKeyExprList = new ArrayList<Mutable<ILogicalExpression>>();

        for (IOptimizableFuncExpr optFuncExpr : optFuncExprs) {
            ComparisonKind ck = AlgebricksBuiltinFunctions.getComparisonType(optFuncExpr.getFuncExpr()
                    .getFunctionIdentifier());
            ILogicalExpression searchKeyExpr = new ConstantExpression(optFuncExpr.getConstantVal(0));
            LogicalVariable var = context.newVar();
            assignKeyExprList.add(new MutableObject<ILogicalExpression>(searchKeyExpr));
            assignKeyVarList.add(var);
            if (ck == ComparisonKind.GE || ck == ComparisonKind.GT) {
                minFilterVars.add(var);
            } else if (ck == ComparisonKind.LE || ck == ComparisonKind.LT) {
                maxFilterVars.add(var);
            } else if (ck == ComparisonKind.EQ) {
                minFilterVars.add(var);
                maxFilterVars.add(var);
            }
        }
        return new AssignOperator(assignKeyVarList, assignKeyExprList);
    }

    private void changePlan(List<IOptimizableFuncExpr> optFuncExprs, AbstractLogicalOperator op, Dataset dataset,
            IOptimizationContext context) throws AlgebricksException {

        AbstractLogicalOperator descendantOp = (AbstractLogicalOperator) op.getInputs().get(0).getValue();
        while (descendantOp != null) {
            if (descendantOp.getOperatorTag() == LogicalOperatorTag.DATASOURCESCAN) {
                DataSourceScanOperator dataSourceScanOp = (DataSourceScanOperator) descendantOp;
                AqlDataSource ds = (AqlDataSource) dataSourceScanOp.getDataSource();
                if (dataset.getDatasetName().compareTo(((DatasetDataSource) ds).getDataset().getDatasetName()) == 0) {
                    List<LogicalVariable> minFilterVars = new ArrayList<LogicalVariable>();
                    List<LogicalVariable> maxFilterVars = new ArrayList<LogicalVariable>();

                    AssignOperator assignOp = createAssignOperator(optFuncExprs, minFilterVars, maxFilterVars, context);

                    dataSourceScanOp.setMinFilterVars(minFilterVars);
                    dataSourceScanOp.setMaxFilterVars(maxFilterVars);

                    List<Mutable<ILogicalExpression>> additionalFilteringExpressions = new ArrayList<Mutable<ILogicalExpression>>();;
                    for (LogicalVariable var : assignOp.getVariables()) {
                        additionalFilteringExpressions.add(new MutableObject<ILogicalExpression>(
                                new VariableReferenceExpression(var)));
                    }

                    dataSourceScanOp.setAdditionalFilteringExpressions(additionalFilteringExpressions);

                    assignOp.getInputs().add(
                            new MutableObject<ILogicalOperator>(dataSourceScanOp.getInputs().get(0).getValue()));
                    dataSourceScanOp.getInputs().get(0).setValue(assignOp);
                }
            } else if (descendantOp.getOperatorTag() == LogicalOperatorTag.UNNEST_MAP) {
                UnnestMapOperator unnestMapOp = (UnnestMapOperator) descendantOp;
                ILogicalExpression unnestExpr = unnestMapOp.getExpressionRef().getValue();
                if (unnestExpr.getExpressionTag() == LogicalExpressionTag.FUNCTION_CALL) {
                    AbstractFunctionCallExpression f = (AbstractFunctionCallExpression) unnestExpr;
                    FunctionIdentifier fid = f.getFunctionIdentifier();
                    if (!fid.equals(AsterixBuiltinFunctions.INDEX_SEARCH)) {
                        throw new IllegalStateException();
                    }
                    AccessMethodJobGenParams jobGenParams = new AccessMethodJobGenParams();
                    jobGenParams.readFromFuncArgs(f.getArguments());
                    if (dataset.getDatasetName().compareTo(jobGenParams.datasetName) == 0) {
                        List<LogicalVariable> minFilterVars = new ArrayList<LogicalVariable>();
                        List<LogicalVariable> maxFilterVars = new ArrayList<LogicalVariable>();

                        AssignOperator assignOp = createAssignOperator(optFuncExprs, minFilterVars, maxFilterVars,
                                context);

                        unnestMapOp.setMinFilterVars(minFilterVars);
                        unnestMapOp.setMaxFilterVars(maxFilterVars);

                        List<Mutable<ILogicalExpression>> additionalFilteringExpressions = new ArrayList<Mutable<ILogicalExpression>>();;
                        for (LogicalVariable var : assignOp.getVariables()) {
                            additionalFilteringExpressions.add(new MutableObject<ILogicalExpression>(
                                    new VariableReferenceExpression(var)));
                        }
                        unnestMapOp.setAdditionalFilteringExpressions(additionalFilteringExpressions);
                        assignOp.getInputs().add(
                                new MutableObject<ILogicalOperator>(unnestMapOp.getInputs().get(0).getValue()));
                        unnestMapOp.getInputs().get(0).setValue(assignOp);
                    }
                }
            }
            if (descendantOp.getInputs().isEmpty()) {
                break;
            }
            descendantOp = (AbstractLogicalOperator) descendantOp.getInputs().get(0).getValue();
        }
    }

    private Dataset getDataset(AbstractLogicalOperator op, IOptimizationContext context) throws AlgebricksException {
        AbstractLogicalOperator descendantOp = (AbstractLogicalOperator) op.getInputs().get(0).getValue();
        while (descendantOp != null) {
            if (descendantOp.getOperatorTag() == LogicalOperatorTag.DATASOURCESCAN) {
                DataSourceScanOperator dataSourceScanOp = (DataSourceScanOperator) descendantOp;
                AqlDataSource ds = (AqlDataSource) dataSourceScanOp.getDataSource();
                return ((DatasetDataSource) ds).getDataset();
            } else if (descendantOp.getOperatorTag() == LogicalOperatorTag.UNNEST_MAP) {
                UnnestMapOperator unnestMapOp = (UnnestMapOperator) descendantOp;
                ILogicalExpression unnestExpr = unnestMapOp.getExpressionRef().getValue();
                if (unnestExpr.getExpressionTag() == LogicalExpressionTag.FUNCTION_CALL) {
                    AbstractFunctionCallExpression f = (AbstractFunctionCallExpression) unnestExpr;
                    FunctionIdentifier fid = f.getFunctionIdentifier();
                    if (!fid.equals(AsterixBuiltinFunctions.INDEX_SEARCH)) {
                        throw new IllegalStateException();
                    }
                    AccessMethodJobGenParams jobGenParams = new AccessMethodJobGenParams();
                    jobGenParams.readFromFuncArgs(f.getArguments());
                    return ((AqlMetadataProvider) context.getMetadataProvider()).findDataset(
                            jobGenParams.dataverseName, jobGenParams.datasetName);
                }
            }
            if (descendantOp.getInputs().isEmpty()) {
                break;
            }
            descendantOp = (AbstractLogicalOperator) descendantOp.getInputs().get(0).getValue();
        }
        return null;
    }

    private boolean checkIfRuleIsApplicable(Mutable<ILogicalOperator> opRef, IOptimizationContext context) {
        // First check that the operator is a select and its condition is a function call.
        AbstractLogicalOperator op = (AbstractLogicalOperator) opRef.getValue();
        if (context.checkIfInDontApplySet(this, op)) {
            return false;
        }
        if (op.getOperatorTag() != LogicalOperatorTag.SELECT) {
            return false;
        }

        ILogicalExpression condExpr = ((SelectOperator) op).getCondition().getValue();
        if (condExpr.getExpressionTag() != LogicalExpressionTag.FUNCTION_CALL) {
            return false;
        }
        return true;
    }

    private AccessMethodAnalysisContext analyzeCondition(ILogicalExpression cond) {
        AccessMethodAnalysisContext analysisCtx = new AccessMethodAnalysisContext();
        AbstractFunctionCallExpression funcExpr = (AbstractFunctionCallExpression) cond;
        FunctionIdentifier funcIdent = funcExpr.getFunctionIdentifier();
        if (funcIdent != AlgebricksBuiltinFunctions.OR) {
            analyzeFunctionExpr(funcExpr, analysisCtx);
            for (Mutable<ILogicalExpression> arg : funcExpr.getArguments()) {
                ILogicalExpression argExpr = arg.getValue();
                if (argExpr.getExpressionTag() != LogicalExpressionTag.FUNCTION_CALL) {
                    continue;
                }
                analyzeFunctionExpr((AbstractFunctionCallExpression) argExpr, analysisCtx);
            }
        }
        return analysisCtx;
    }

    private void analyzeFunctionExpr(AbstractFunctionCallExpression funcExpr, AccessMethodAnalysisContext analysisCtx) {
        FunctionIdentifier funcIdent = funcExpr.getFunctionIdentifier();
        if (funcIdent == AlgebricksBuiltinFunctions.LE || funcIdent == AlgebricksBuiltinFunctions.GE
                || funcIdent == AlgebricksBuiltinFunctions.LT || funcIdent == AlgebricksBuiltinFunctions.GT
                || funcIdent == AlgebricksBuiltinFunctions.EQ) {
            AccessMethodUtils.analyzeFuncExprArgsForOneConstAndVar(funcExpr, analysisCtx);
        }
    }

    private boolean findMacthedExprFieldName(IOptimizableFuncExpr optFuncExpr, AbstractLogicalOperator op,
            Dataset dataset, ARecordType recType, List<Index> datasetIndexes) throws AlgebricksException {
        AbstractLogicalOperator descendantOp = (AbstractLogicalOperator) op.getInputs().get(0).getValue();
        while (descendantOp != null) {
            if (descendantOp.getOperatorTag() == LogicalOperatorTag.ASSIGN) {
                AssignOperator assignOp = (AssignOperator) descendantOp;
                List<LogicalVariable> varList = assignOp.getVariables();
                for (int varIndex = 0; varIndex < varList.size(); varIndex++) {
                    LogicalVariable var = varList.get(varIndex);
                    int funcVarIndex = optFuncExpr.findLogicalVar(var);
                    if (funcVarIndex == -1) {
                        continue;
                    }
                    String fieldName = getFieldNameFromSubAssignTree(optFuncExpr, descendantOp, varIndex, recType);
                    if (fieldName == null) {
                        return false;
                    }
                    optFuncExpr.setFieldName(funcVarIndex, fieldName);
                    return true;
                }
            } else if (descendantOp.getOperatorTag() == LogicalOperatorTag.DATASOURCESCAN) {
                DataSourceScanOperator scanOp = (DataSourceScanOperator) descendantOp;
                List<LogicalVariable> varList = scanOp.getVariables();
                for (int varIndex = 0; varIndex < varList.size(); varIndex++) {
                    LogicalVariable var = varList.get(varIndex);
                    int funcVarIndex = optFuncExpr.findLogicalVar(var);
                    if (funcVarIndex == -1) {
                        continue;
                    }
                    // The variable value is one of the partitioning fields.
                    String fieldName = DatasetUtils.getPartitioningKeys(dataset).get(varIndex);
                    if (fieldName == null) {
                        return false;
                    }
                    optFuncExpr.setFieldName(funcVarIndex, fieldName);
                    return true;
                }
            } else if (descendantOp.getOperatorTag() == LogicalOperatorTag.UNNEST_MAP) {
                UnnestMapOperator unnestMapOp = (UnnestMapOperator) descendantOp;
                List<LogicalVariable> varList = unnestMapOp.getVariables();
                for (int varIndex = 0; varIndex < varList.size(); varIndex++) {
                    LogicalVariable var = varList.get(varIndex);
                    int funcVarIndex = optFuncExpr.findLogicalVar(var);
                    if (funcVarIndex == -1) {
                        continue;
                    }

                    String indexName = null;
                    Index index = null;
                    ILogicalExpression unnestExpr = unnestMapOp.getExpressionRef().getValue();
                    if (unnestExpr.getExpressionTag() == LogicalExpressionTag.FUNCTION_CALL) {
                        AbstractFunctionCallExpression f = (AbstractFunctionCallExpression) unnestExpr;
                        FunctionIdentifier fid = f.getFunctionIdentifier();
                        if (!fid.equals(AsterixBuiltinFunctions.INDEX_SEARCH)) {
                            throw new IllegalStateException();
                        }
                        AccessMethodJobGenParams jobGenParams = new AccessMethodJobGenParams();
                        jobGenParams.readFromFuncArgs(f.getArguments());
                        indexName = jobGenParams.indexName;
                        for (Index idx : datasetIndexes) {
                            if (idx.getIndexName().compareTo(indexName) == 0) {
                                index = idx;
                                break;
                            }
                        }
                    }

                    int numSecondaryKeys = AccessMethodUtils.getNumSecondaryKeys(index, recType);
                    String fieldName;
                    if (varIndex >= numSecondaryKeys) {
                        fieldName = DatasetUtils.getPartitioningKeys(dataset).get(varIndex - numSecondaryKeys);
                    } else {
                        fieldName = index.getKeyFieldNames().get(varIndex);
                    }
                    if (fieldName == null) {
                        return false;
                    }
                    optFuncExpr.setFieldName(funcVarIndex, fieldName);
                    return true;
                }
            }

            if (descendantOp.getInputs().isEmpty()) {
                break;
            }
            descendantOp = (AbstractLogicalOperator) descendantOp.getInputs().get(0).getValue();
        }
        return false;
    }

    private String getFieldNameFromSubAssignTree(IOptimizableFuncExpr optFuncExpr, AbstractLogicalOperator op,
            int varIndex, ARecordType recType) {
        AbstractLogicalExpression expr = null;
        if (op.getOperatorTag() == LogicalOperatorTag.ASSIGN) {
            AssignOperator assignOp = (AssignOperator) op;
            expr = (AbstractLogicalExpression) assignOp.getExpressions().get(varIndex).getValue();
        }
        if (expr.getExpressionTag() != LogicalExpressionTag.FUNCTION_CALL) {
            return null;
        }
        AbstractFunctionCallExpression funcExpr = (AbstractFunctionCallExpression) expr;
        FunctionIdentifier funcIdent = funcExpr.getFunctionIdentifier();
        if (funcIdent == AsterixBuiltinFunctions.FIELD_ACCESS_BY_NAME) {
            ILogicalExpression nameArg = funcExpr.getArguments().get(1).getValue();
            if (nameArg.getExpressionTag() != LogicalExpressionTag.CONSTANT) {
                return null;
            }
            ConstantExpression constExpr = (ConstantExpression) nameArg;
            return ((AString) ((AsterixConstantValue) constExpr.getValue()).getObject()).getStringValue();
        } else if (funcIdent == AsterixBuiltinFunctions.FIELD_ACCESS_BY_INDEX) {
            ILogicalExpression idxArg = funcExpr.getArguments().get(1).getValue();
            if (idxArg.getExpressionTag() != LogicalExpressionTag.CONSTANT) {
                return null;
            }
            ConstantExpression constExpr = (ConstantExpression) idxArg;
            int fieldIndex = ((AInt32) ((AsterixConstantValue) constExpr.getValue()).getObject()).getIntegerValue();
            return recType.getFieldNames()[fieldIndex];
        }

        ILogicalExpression argExpr = funcExpr.getArguments().get(0).getValue();
        if (argExpr.getExpressionTag() != LogicalExpressionTag.VARIABLE) {
            return null;
        }

        return null;
    }
}
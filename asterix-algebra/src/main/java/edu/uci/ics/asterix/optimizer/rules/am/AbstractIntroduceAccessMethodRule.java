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
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.apache.commons.lang3.mutable.Mutable;

import edu.uci.ics.asterix.metadata.declared.AqlMetadataProvider;
import edu.uci.ics.asterix.metadata.entities.Dataset;
import edu.uci.ics.asterix.metadata.entities.Index;
import edu.uci.ics.asterix.metadata.utils.DatasetUtils;
import edu.uci.ics.asterix.om.base.AInt32;
import edu.uci.ics.asterix.om.base.AString;
import edu.uci.ics.asterix.om.constants.AsterixConstantValue;
import edu.uci.ics.asterix.om.functions.AsterixBuiltinFunctions;
import edu.uci.ics.asterix.om.types.IAType;
import edu.uci.ics.hyracks.algebricks.common.exceptions.AlgebricksException;
import edu.uci.ics.hyracks.algebricks.common.utils.Pair;
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
import edu.uci.ics.hyracks.algebricks.core.algebra.functions.FunctionIdentifier;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.AbstractLogicalOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.AssignOperator;
import edu.uci.ics.hyracks.algebricks.core.algebra.operators.logical.UnnestOperator;
import edu.uci.ics.hyracks.algebricks.core.rewriter.base.IAlgebraicRewriteRule;

/**
 * Class that embodies the commonalities between rewrite rules for access methods.
 */
public abstract class AbstractIntroduceAccessMethodRule implements IAlgebraicRewriteRule {

    private AqlMetadataProvider metadataProvider;

    public abstract Map<FunctionIdentifier, List<IAccessMethod>> getAccessMethods();

    protected static void registerAccessMethod(IAccessMethod accessMethod,
            Map<FunctionIdentifier, List<IAccessMethod>> accessMethods) {
        List<FunctionIdentifier> funcs = accessMethod.getOptimizableFunctions();
        for (FunctionIdentifier funcIdent : funcs) {
            List<IAccessMethod> l = accessMethods.get(funcIdent);
            if (l == null) {
                l = new ArrayList<IAccessMethod>();
                accessMethods.put(funcIdent, l);
            }
            l.add(accessMethod);
        }
    }

    @Override
    public boolean rewritePre(Mutable<ILogicalOperator> opRef, IOptimizationContext context) {
        return false;
    }

    protected void setMetadataDeclarations(IOptimizationContext context) {
        metadataProvider = (AqlMetadataProvider) context.getMetadataProvider();
    }

    protected void fillSubTreeIndexExprs(OptimizableOperatorSubTree subTree,
            Map<IAccessMethod, AccessMethodAnalysisContext> analyzedAMs, IOptimizationContext context)
            throws AlgebricksException {
        Iterator<Map.Entry<IAccessMethod, AccessMethodAnalysisContext>> amIt = analyzedAMs.entrySet().iterator();
        // Check applicability of indexes by access method type.
        while (amIt.hasNext()) {
            Map.Entry<IAccessMethod, AccessMethodAnalysisContext> entry = amIt.next();
            AccessMethodAnalysisContext amCtx = entry.getValue();
            // For the current access method type, map variables to applicable indexes.
            fillAllIndexExprs(subTree, amCtx, context);
        }
    }

    protected void pruneIndexCandidates(Map<IAccessMethod, AccessMethodAnalysisContext> analyzedAMs) {
        Iterator<Map.Entry<IAccessMethod, AccessMethodAnalysisContext>> amIt = analyzedAMs.entrySet().iterator();
        // Check applicability of indexes by access method type.
        while (amIt.hasNext()) {
            Map.Entry<IAccessMethod, AccessMethodAnalysisContext> entry = amIt.next();
            AccessMethodAnalysisContext amCtx = entry.getValue();
            pruneIndexCandidates(entry.getKey(), amCtx);
            // Remove access methods for which there are definitely no applicable indexes.
            if (amCtx.indexExprs.isEmpty()) {
                amIt.remove();
            }
        }
    }

    /**
     * Simply picks the first index that it finds.
     * TODO: Improve this decision process by making it more systematic.
     */
    protected Pair<IAccessMethod, Index> chooseIndex(Map<IAccessMethod, AccessMethodAnalysisContext> analyzedAMs) {
        Iterator<Map.Entry<IAccessMethod, AccessMethodAnalysisContext>> amIt = analyzedAMs.entrySet().iterator();
        while (amIt.hasNext()) {
            Map.Entry<IAccessMethod, AccessMethodAnalysisContext> amEntry = amIt.next();
            AccessMethodAnalysisContext analysisCtx = amEntry.getValue();
            Iterator<Map.Entry<Index, List<Integer>>> indexIt = analysisCtx.indexExprs.entrySet().iterator();
            if (indexIt.hasNext()) {
                Map.Entry<Index, List<Integer>> indexEntry = indexIt.next();
                return new Pair<IAccessMethod, Index>(amEntry.getKey(), indexEntry.getKey());
            }
        }
        return null;
    }

    /**
     * Removes irrelevant access methods candidates, based on whether the
     * expressions in the query match those in the index. For example, some
     * index may require all its expressions to be matched, and some indexes may
     * only require a match on a prefix of fields to be applicable. This methods
     * removes all index candidates indexExprs that are definitely not
     * applicable according to the expressions involved.
     */
    public void pruneIndexCandidates(IAccessMethod accessMethod, AccessMethodAnalysisContext analysisCtx) {
        Iterator<Map.Entry<Index, List<Integer>>> it = analysisCtx.indexExprs.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<Index, List<Integer>> entry = it.next();
            Index index = entry.getKey();
            boolean allUsed = true;
            int lastFieldMatched = -1;
            for (int i = 0; i < index.getKeyFieldNames().size(); i++) {
                String keyField = index.getKeyFieldNames().get(i);
                boolean foundKeyField = false;
                Iterator<Integer> exprsIter = entry.getValue().iterator();
                while (exprsIter.hasNext()) {
                    Integer ix = exprsIter.next();
                    IOptimizableFuncExpr optFuncExpr = analysisCtx.matchedFuncExprs.get(ix);
                    // If expr is not optimizable by concrete index then remove expr and continue.
                    if (!accessMethod.exprIsOptimizable(index, optFuncExpr)) {
                        exprsIter.remove();
                        continue;
                    }
                    // Check if any field name in the optFuncExpr matches.
                    if (optFuncExpr.findFieldName(keyField) != -1) {
                        foundKeyField = true;
                        if (lastFieldMatched == i - 1) {
                            lastFieldMatched = i;
                        }
                        break;
                    }
                }
                if (!foundKeyField) {
                    allUsed = false;
                    break;
                }
            }
            // If the access method requires all exprs to be matched but they are not, remove this candidate.
            if (!allUsed && accessMethod.matchAllIndexExprs()) {
                it.remove();
            }
            // A prefix of the index exprs may have been matched.
            if (lastFieldMatched < 0 && accessMethod.matchPrefixIndexExprs()) {
                it.remove();
            }
        }
    }

    /**
     * Analyzes the given selection condition, filling analyzedAMs with applicable access method types.
     * At this point we are not yet consulting the metadata whether an actual index exists or not.
     */
    protected boolean analyzeCondition(ILogicalExpression cond, List<AbstractLogicalOperator> assignsAndUnnests,
            Map<IAccessMethod, AccessMethodAnalysisContext> analyzedAMs) {
        AbstractFunctionCallExpression funcExpr = (AbstractFunctionCallExpression) cond;
        FunctionIdentifier funcIdent = funcExpr.getFunctionIdentifier();
        // Don't consider optimizing a disjunctive condition with an index (too complicated for now).
        if (funcIdent == AlgebricksBuiltinFunctions.OR) {
            return false;
        }
        boolean found = analyzeFunctionExpr(funcExpr, assignsAndUnnests, analyzedAMs);
        for (Mutable<ILogicalExpression> arg : funcExpr.getArguments()) {
            ILogicalExpression argExpr = arg.getValue();
            if (argExpr.getExpressionTag() != LogicalExpressionTag.FUNCTION_CALL) {
                continue;
            }
            AbstractFunctionCallExpression argFuncExpr = (AbstractFunctionCallExpression) argExpr;
            boolean matchFound = analyzeFunctionExpr(argFuncExpr, assignsAndUnnests, analyzedAMs);
            found = found || matchFound;
        }
        return found;
    }

    /**
     * Finds applicable access methods for the given function expression based
     * on the function identifier, and an analysis of the function's arguments.
     * Updates the analyzedAMs accordingly.
     */
    protected boolean analyzeFunctionExpr(AbstractFunctionCallExpression funcExpr,
            List<AbstractLogicalOperator> assignsAndUnnests, Map<IAccessMethod, AccessMethodAnalysisContext> analyzedAMs) {
        FunctionIdentifier funcIdent = funcExpr.getFunctionIdentifier();
        if (funcIdent == AlgebricksBuiltinFunctions.AND) {
            return false;
        }
        // Retrieves the list of access methods that are relevant based on the funcIdent.
        List<IAccessMethod> relevantAMs = getAccessMethods().get(funcIdent);
        if (relevantAMs == null) {
            return false;
        }
        boolean atLeastOneMatchFound = false;
        // Place holder for a new analysis context in case we need one.
        AccessMethodAnalysisContext newAnalysisCtx = new AccessMethodAnalysisContext();
        for (IAccessMethod accessMethod : relevantAMs) {
            AccessMethodAnalysisContext analysisCtx = analyzedAMs.get(accessMethod);
            // Use the current place holder.
            if (analysisCtx == null) {
                analysisCtx = newAnalysisCtx;
            }
            // Analyzes the funcExpr's arguments to see if the accessMethod is truly applicable.
            boolean matchFound = accessMethod.analyzeFuncExprArgs(funcExpr, assignsAndUnnests, analysisCtx);
            if (matchFound) {
                // If we've used the current new context placeholder, replace it with a new one.
                if (analysisCtx == newAnalysisCtx) {
                    analyzedAMs.put(accessMethod, analysisCtx);
                    newAnalysisCtx = new AccessMethodAnalysisContext();
                }
                atLeastOneMatchFound = true;
            }
        }
        return atLeastOneMatchFound;
    }

    /**
     * Finds secondary indexes whose keys include fieldName, and adds a mapping in analysisCtx.indexEsprs
     * from that index to the a corresponding optimizable function expression.
     * 
     * @return true if a candidate index was added to foundIndexExprs, false
     *         otherwise
     * @throws AlgebricksException
     */
    protected boolean fillIndexExprs(String fieldName, int matchedFuncExprIndex, Dataset dataset,
            AccessMethodAnalysisContext analysisCtx) throws AlgebricksException {
        List<Index> datasetIndexes = metadataProvider.getDatasetIndexes(dataset.getDataverseName(),
                dataset.getDatasetName());
        List<Index> indexCandidates = new ArrayList<Index>();
        // Add an index to the candidates if one of the indexed fields is fieldName
        for (Index index : datasetIndexes) {
            if (index.getKeyFieldNames().contains(fieldName)) {
                indexCandidates.add(index);
            }
        }
        // No index candidates for fieldName.
        if (indexCandidates.isEmpty()) {
            return false;
        }
        // Go through the candidates and fill indexExprs.
        for (Index index : indexCandidates) {
            analysisCtx.addIndexExpr(dataset, index, matchedFuncExprIndex);
        }
        return true;
    }

    protected void fillAllIndexExprs(OptimizableOperatorSubTree subTree, AccessMethodAnalysisContext analysisCtx,
            IOptimizationContext context) throws AlgebricksException {
        for (int optFuncExprIndex = 0; optFuncExprIndex < analysisCtx.matchedFuncExprs.size(); optFuncExprIndex++) {
            IOptimizableFuncExpr optFuncExpr = analysisCtx.matchedFuncExprs.get(optFuncExprIndex);
            // Try to match variables from optFuncExpr to assigns or unnests.
            for (int assignOrUnnestIndex = 0; assignOrUnnestIndex < subTree.assignsAndUnnests.size(); assignOrUnnestIndex++) {
                AbstractLogicalOperator op = subTree.assignsAndUnnests.get(assignOrUnnestIndex);
                if (op.getOperatorTag() == LogicalOperatorTag.ASSIGN) {
                    AssignOperator assignOp = (AssignOperator) op;
                    List<LogicalVariable> varList = assignOp.getVariables();
                    for (int varIndex = 0; varIndex < varList.size(); varIndex++) {
                        LogicalVariable var = varList.get(varIndex);
                        int funcVarIndex = optFuncExpr.findLogicalVar(var);
                        // No matching var in optFuncExpr.
                        if (funcVarIndex == -1) {
                            continue;
                        }
                        // At this point we have matched the optimizable func expr at optFuncExprIndex to an assigned variable.
                        // Remember matching subtree.
                        optFuncExpr.setOptimizableSubTree(funcVarIndex, subTree);
                        String fieldName = getFieldNameFromSubTree(optFuncExpr, subTree, assignOrUnnestIndex, varIndex);
                        if (fieldName == null) {
                            continue;
                        }
                        // Set the fieldName in the corresponding matched function expression.
                        optFuncExpr.setFieldName(funcVarIndex, fieldName);
                        setTypeTag(context, subTree, optFuncExpr, funcVarIndex);
                        if (subTree.hasDataSourceScan()) {
                            fillIndexExprs(fieldName, optFuncExprIndex, subTree.dataset, analysisCtx);
                        }
                    }
                } else {
                    UnnestOperator unnestOp = (UnnestOperator) op;
                    LogicalVariable var = unnestOp.getVariable();
                    int funcVarIndex = optFuncExpr.findLogicalVar(var);
                    // No matching var in optFuncExpr.
                    if (funcVarIndex == -1) {
                        continue;
                    }
                    // At this point we have matched the optimizable func expr at optFuncExprIndex to an unnest variable.
                    // Remember matching subtree.
                    optFuncExpr.setOptimizableSubTree(funcVarIndex, subTree);
                    String fieldName = getFieldNameFromSubTree(optFuncExpr, subTree, assignOrUnnestIndex, 0);
                    if (fieldName == null) {
                        continue;
                    }
                    // Set the fieldName in the corresponding matched function expression.
                    optFuncExpr.setFieldName(funcVarIndex, fieldName);
                    setTypeTag(context, subTree, optFuncExpr, funcVarIndex);
                    if (subTree.hasDataSourceScan()) {
                        fillIndexExprs(fieldName, optFuncExprIndex, subTree.dataset, analysisCtx);
                    }
                }
            }

            // Try to match variables from optFuncExpr to datasourcescan if not already matched in assigns.
            List<LogicalVariable> dsVarList = subTree.getDataSourceVariables();
            for (int varIndex = 0; varIndex < dsVarList.size(); varIndex++) {
                LogicalVariable var = dsVarList.get(varIndex);
                int funcVarIndex = optFuncExpr.findLogicalVar(var);
                // No matching var in optFuncExpr.
                if (funcVarIndex == -1) {
                    continue;
                }
                // The variable value is one of the partitioning fields.
                String fieldName = DatasetUtils.getPartitioningKeys(subTree.dataset).get(varIndex);
                // Set the fieldName in the corresponding matched function expression, and remember matching subtree.
                optFuncExpr.setFieldName(funcVarIndex, fieldName);
                optFuncExpr.setOptimizableSubTree(funcVarIndex, subTree);
                setTypeTag(context, subTree, optFuncExpr, funcVarIndex);
                if (subTree.hasDataSourceScan()) {
                    fillIndexExprs(fieldName, optFuncExprIndex, subTree.dataset, analysisCtx);
                }
            }
        }
    }

    private void setTypeTag(IOptimizationContext context, OptimizableOperatorSubTree subTree,
            IOptimizableFuncExpr optFuncExpr, int funcVarIndex) throws AlgebricksException {
        // Set the typeTag if the type is not null
        IAType type = (IAType) context.getOutputTypeEnvironment(subTree.root).getVarType(
                optFuncExpr.getLogicalVar(funcVarIndex));
        optFuncExpr.setTypeTag(funcVarIndex, type.getTypeTag());
    }

    /**
     * Returns the field name corresponding to the assigned variable at varIndex.
     * Returns null if the expr at varIndex does not yield to a field access function after following a set of allowed functions.
     */
    protected String getFieldNameFromSubTree(IOptimizableFuncExpr optFuncExpr, OptimizableOperatorSubTree subTree,
            int opIndex, int assignVarIndex) {
        // Get expression corresponding to opVar at varIndex.
        AbstractLogicalExpression expr = null;
        AbstractLogicalOperator op = subTree.assignsAndUnnests.get(opIndex);
        if (op.getOperatorTag() == LogicalOperatorTag.ASSIGN) {
            AssignOperator assignOp = (AssignOperator) op;
            expr = (AbstractLogicalExpression) assignOp.getExpressions().get(assignVarIndex).getValue();
        } else {
            UnnestOperator unnestOp = (UnnestOperator) op;
            expr = (AbstractLogicalExpression) unnestOp.getExpressionRef().getValue();
            if (expr.getExpressionTag() != LogicalExpressionTag.FUNCTION_CALL) {
                return null;
            }
            AbstractFunctionCallExpression childFuncExpr = (AbstractFunctionCallExpression) expr;
            if (childFuncExpr.getFunctionIdentifier() != AsterixBuiltinFunctions.SCAN_COLLECTION) {
                return null;
            }
            expr = (AbstractLogicalExpression) childFuncExpr.getArguments().get(0).getValue();
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
            return subTree.recordType.getFieldNames()[fieldIndex];
        }
        if (funcIdent != AsterixBuiltinFunctions.WORD_TOKENS && funcIdent != AsterixBuiltinFunctions.GRAM_TOKENS
                && funcIdent != AsterixBuiltinFunctions.SUBSTRING
                && funcIdent != AsterixBuiltinFunctions.SUBSTRING_BEFORE
                && funcIdent != AsterixBuiltinFunctions.SUBSTRING_AFTER) {
            return null;
        }
        // We use a part of the field in edit distance computation
        if (optFuncExpr.getFuncExpr().getFunctionIdentifier() == AsterixBuiltinFunctions.EDIT_DISTANCE_CHECK) {
            optFuncExpr.setPartialField(true);
        }
        // We expect the function's argument to be a variable, otherwise we cannot apply an index.
        ILogicalExpression argExpr = funcExpr.getArguments().get(0).getValue();
        if (argExpr.getExpressionTag() != LogicalExpressionTag.VARIABLE) {
            return null;
        }
        LogicalVariable curVar = ((VariableReferenceExpression) argExpr).getVariableReference();
        // We look for the assign or unnest operator that produces curVar below the current operator
        for (int assignOrUnnestIndex = opIndex + 1; assignOrUnnestIndex < subTree.assignsAndUnnests.size(); assignOrUnnestIndex++) {
            AbstractLogicalOperator curOp = subTree.assignsAndUnnests.get(assignOrUnnestIndex);
            if (curOp.getOperatorTag() == LogicalOperatorTag.ASSIGN) {
                AssignOperator assignOp = (AssignOperator) curOp;
                List<LogicalVariable> varList = assignOp.getVariables();
                for (int varIndex = 0; varIndex < varList.size(); varIndex++) {
                    LogicalVariable var = varList.get(varIndex);
                    if (var.equals(curVar)) {
                        return getFieldNameFromSubTree(optFuncExpr, subTree, assignOrUnnestIndex, varIndex);
                    }
                }
            } else {
                UnnestOperator unnestOp = (UnnestOperator) curOp;
                LogicalVariable var = unnestOp.getVariable();
                if (var.equals(curVar)) {
                    getFieldNameFromSubTree(optFuncExpr, subTree, assignOrUnnestIndex, 0);
                }
            }
        }
        return null;
    }
}

/*
 * Copyright 2009-2012 by The Regents of the University of California
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
package edu.uci.ics.hyracks.storage.am.lsm.invertedindex.impls;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import edu.uci.ics.hyracks.api.dataflow.value.IBinaryComparatorFactory;
import edu.uci.ics.hyracks.api.dataflow.value.ITypeTraits;
import edu.uci.ics.hyracks.api.exceptions.HyracksDataException;
import edu.uci.ics.hyracks.api.io.FileReference;
import edu.uci.ics.hyracks.dataflow.common.data.accessors.ITupleReference;
import edu.uci.ics.hyracks.storage.am.btree.exceptions.BTreeDuplicateKeyException;
import edu.uci.ics.hyracks.storage.am.btree.frames.BTreeLeafFrameType;
import edu.uci.ics.hyracks.storage.am.btree.impls.BTree;
import edu.uci.ics.hyracks.storage.am.btree.impls.BTree.BTreeAccessor;
import edu.uci.ics.hyracks.storage.am.btree.impls.RangePredicate;
import edu.uci.ics.hyracks.storage.am.btree.util.BTreeUtils;
import edu.uci.ics.hyracks.storage.am.common.api.ICursorInitialState;
import edu.uci.ics.hyracks.storage.am.common.api.IInMemoryFreePageManager;
import edu.uci.ics.hyracks.storage.am.common.api.IIndexAccessor;
import edu.uci.ics.hyracks.storage.am.common.api.IIndexBulkLoader;
import edu.uci.ics.hyracks.storage.am.common.api.IIndexCursor;
import edu.uci.ics.hyracks.storage.am.common.api.IIndexOperationContext;
import edu.uci.ics.hyracks.storage.am.common.api.IModificationOperationCallback;
import edu.uci.ics.hyracks.storage.am.common.api.ISearchOperationCallback;
import edu.uci.ics.hyracks.storage.am.common.api.ISearchPredicate;
import edu.uci.ics.hyracks.storage.am.common.api.ITreeIndex;
import edu.uci.ics.hyracks.storage.am.common.api.IndexException;
import edu.uci.ics.hyracks.storage.am.common.api.TreeIndexException;
import edu.uci.ics.hyracks.storage.am.common.impls.NoOpOperationCallback;
import edu.uci.ics.hyracks.storage.am.common.ophelpers.IndexOperation;
import edu.uci.ics.hyracks.storage.am.common.ophelpers.MultiComparator;
import edu.uci.ics.hyracks.storage.am.common.tuples.PermutingTupleReference;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.IInMemoryBufferCache;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMComponent;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMComponentFactory;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMIOOperation;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMIOOperationCallback;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMIOOperationScheduler;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMIndexAccessor;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMIndexAccessorInternal;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMIndexFileManager;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMMergePolicy;
import edu.uci.ics.hyracks.storage.am.lsm.common.api.ILSMOperationTrackerFactory;
import edu.uci.ics.hyracks.storage.am.lsm.common.freepage.InMemoryBufferCache;
import edu.uci.ics.hyracks.storage.am.lsm.common.impls.AbstractLSMIndex;
import edu.uci.ics.hyracks.storage.am.lsm.common.impls.BTreeFactory;
import edu.uci.ics.hyracks.storage.am.lsm.common.impls.BlockingIOOperationCallback;
import edu.uci.ics.hyracks.storage.am.lsm.common.impls.LSMComponentFileReferences;
import edu.uci.ics.hyracks.storage.am.lsm.common.impls.LSMComponentState;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.api.IInvertedIndex;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.api.IInvertedListCursor;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.inmemory.InMemoryInvertedIndex;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.inmemory.InMemoryInvertedIndexAccessor;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.ondisk.OnDiskInvertedIndex;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.ondisk.OnDiskInvertedIndexFactory;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.search.InvertedIndexSearchPredicate;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.tokenizers.IBinaryTokenizerFactory;
import edu.uci.ics.hyracks.storage.am.lsm.invertedindex.util.InvertedIndexUtils;
import edu.uci.ics.hyracks.storage.common.buffercache.IBufferCache;
import edu.uci.ics.hyracks.storage.common.file.IFileMapProvider;

public class LSMInvertedIndex extends AbstractLSMIndex implements IInvertedIndex {

    // In-memory components.
    protected final LSMInvertedIndexComponent mutableComponent;
    protected final IInMemoryFreePageManager memFreePageManager;
    protected final IBinaryTokenizerFactory tokenizerFactory;

    // On-disk components.
    // For creating inverted indexes in flush and merge.
    protected final ILSMComponentFactory componentFactory;

    // Type traits and comparators for tokens and inverted-list elements.
    protected final ITypeTraits[] invListTypeTraits;
    protected final IBinaryComparatorFactory[] invListCmpFactories;
    protected final ITypeTraits[] tokenTypeTraits;
    protected final IBinaryComparatorFactory[] tokenCmpFactories;

    public LSMInvertedIndex(IInMemoryBufferCache memBufferCache, IInMemoryFreePageManager memFreePageManager,
            OnDiskInvertedIndexFactory diskInvIndexFactory, BTreeFactory deletedKeysBTreeFactory,
            ILSMIndexFileManager fileManager, IFileMapProvider diskFileMapProvider, ITypeTraits[] invListTypeTraits,
            IBinaryComparatorFactory[] invListCmpFactories, ITypeTraits[] tokenTypeTraits,
            IBinaryComparatorFactory[] tokenCmpFactories, IBinaryTokenizerFactory tokenizerFactory,
            ILSMMergePolicy mergePolicy, ILSMOperationTrackerFactory opTrackerFactory,
            ILSMIOOperationScheduler ioScheduler) throws IndexException {
        super(memFreePageManager, diskInvIndexFactory.getBufferCache(), fileManager, diskFileMapProvider, mergePolicy,
                opTrackerFactory, ioScheduler);
        this.memFreePageManager = memFreePageManager;
        this.tokenizerFactory = tokenizerFactory;
        this.invListTypeTraits = invListTypeTraits;
        this.invListCmpFactories = invListCmpFactories;
        this.tokenTypeTraits = tokenTypeTraits;
        this.tokenCmpFactories = tokenCmpFactories;
        // Create in-memory component.
        InMemoryInvertedIndex memInvIndex = createInMemoryInvertedIndex(memBufferCache);
        BTree deleteKeysBTree = BTreeUtils.createBTree(memBufferCache, memFreePageManager,
                ((InMemoryBufferCache) memBufferCache).getFileMapProvider(), invListTypeTraits, invListCmpFactories,
                BTreeLeafFrameType.REGULAR_NSM, new FileReference(new File("membtree")));
        mutableComponent = new LSMInvertedIndexComponent(memInvIndex, deleteKeysBTree);
        componentFactory = new LSMInvertedIndexComponentFactory(diskInvIndexFactory, deletedKeysBTreeFactory);
    }

    protected InMemoryInvertedIndex createInMemoryInvertedIndex(IInMemoryBufferCache memBufferCache)
            throws IndexException {
        return InvertedIndexUtils.createInMemoryBTreeInvertedindex(memBufferCache, memFreePageManager,
                invListTypeTraits, invListCmpFactories, tokenTypeTraits, tokenCmpFactories, tokenizerFactory);
    }

    @Override
    public synchronized void create() throws HyracksDataException {
        if (isActivated) {
            throw new HyracksDataException("Failed to create the index since it is activated.");
        }

        fileManager.deleteDirs();
        fileManager.createDirs();
        immutableComponents.clear();
    }

    @Override
    public synchronized void activate() throws HyracksDataException {
        if (isActivated) {
            return;
        }
        try {
            ((InMemoryBufferCache) mutableComponent.getInvIndex().getBufferCache()).open();
            mutableComponent.getInvIndex().create();
            mutableComponent.getInvIndex().activate();
            mutableComponent.getDeletedKeysBTree().create();
            mutableComponent.getDeletedKeysBTree().activate();
            immutableComponents.clear();
            List<LSMComponentFileReferences> validFileReferences = fileManager.cleanupAndGetValidFiles();
            for (LSMComponentFileReferences lsmComonentFileReference : validFileReferences) {
                LSMInvertedIndexComponent component;
                try {
                    component = createDiskInvIndexComponent(componentFactory,
                            lsmComonentFileReference.getInsertIndexFileReference(),
                            lsmComonentFileReference.getDeleteIndexFileReference(), false);
                } catch (IndexException e) {
                    throw new HyracksDataException(e);
                }
                immutableComponents.add(component);
            }
            isActivated = true;
            // TODO: Maybe we can make activate throw an index exception?
        } catch (IndexException e) {
            throw new HyracksDataException(e);
        }
    }

    @Override
    public List<ILSMComponent> getOperationalComponents(IIndexOperationContext ctx) {
        List<ILSMComponent> operationalComponents = new ArrayList<ILSMComponent>();
        switch (ctx.getOperation()) {
            case SEARCH:
                // TODO: We should add the mutable component at some point.
                operationalComponents.addAll(immutableComponents);
                break;
            case MERGE:
                // TODO: determining the participating components in a merge should probably the task of the merge policy.
                if (immutableComponents.size() > 1) {
                    for (ILSMComponent c : immutableComponents) {
                        if (c.negativeCompareAndSet(LSMComponentState.MERGING, LSMComponentState.MERGING)) {
                            operationalComponents.add(c);
                        }
                    }
                }
                break;
            default:
                throw new UnsupportedOperationException("Operation " + ctx.getOperation() + " not supported.");
        }
        return operationalComponents;
    }

    protected LSMInvertedIndexComponent createDiskInvIndexComponent(ILSMComponentFactory factory,
            FileReference dictBTreeFileRef, FileReference btreeFileRef, boolean create) throws HyracksDataException,
            IndexException {
        LSMInvertedIndexComponent component = (LSMInvertedIndexComponent) factory
                .createLSMComponentInstance(new LSMComponentFileReferences(dictBTreeFileRef, btreeFileRef));
        if (create) {
            component.getInvIndex().create();
            component.getDeletedKeysBTree().create();
        }
        // Will be closed during cleanup of merge().
        component.getInvIndex().activate();
        component.getDeletedKeysBTree().activate();
        return component;
    }

    @Override
    public void clear() throws HyracksDataException {
        if (!isActivated) {
            throw new HyracksDataException("Failed to clear the index since it is not activated.");
        }
        resetMutableComponent();
        for (ILSMComponent c : immutableComponents) {
            LSMInvertedIndexComponent component = (LSMInvertedIndexComponent) c;
            component.getInvIndex().deactivate();
            component.getDeletedKeysBTree().deactivate();
            component.getInvIndex().destroy();
            component.getDeletedKeysBTree().destroy();
        }
        immutableComponents.clear();
    }

    @Override
    public synchronized void deactivate() throws HyracksDataException {
        if (!isActivated) {
            return;
        }

        isActivated = false;

        BlockingIOOperationCallback blockingCallBack = new BlockingIOOperationCallback();
        ILSMIndexAccessor accessor = (ILSMIndexAccessor) createAccessor(NoOpOperationCallback.INSTANCE,
                NoOpOperationCallback.INSTANCE);
        accessor.scheduleFlush(blockingCallBack);
        try {
            blockingCallBack.waitForIO();
        } catch (InterruptedException e) {
            throw new HyracksDataException(e);
        }

        for (ILSMComponent c : immutableComponents) {
            LSMInvertedIndexComponent component = (LSMInvertedIndexComponent) c;
            component.getInvIndex().deactivate();
            component.getDeletedKeysBTree().deactivate();
        }
        mutableComponent.getInvIndex().deactivate();
        mutableComponent.getDeletedKeysBTree().deactivate();
        mutableComponent.getInvIndex().destroy();
        mutableComponent.getDeletedKeysBTree().destroy();
        ((InMemoryBufferCache) mutableComponent.getInvIndex().getBufferCache()).close();
    }

    @Override
    public synchronized void destroy() throws HyracksDataException {
        if (isActivated) {
            throw new HyracksDataException("Failed to destroy the index since it is activated.");
        }

        mutableComponent.getInvIndex().destroy();
        mutableComponent.getDeletedKeysBTree().destroy();
        for (ILSMComponent c : immutableComponents) {
            LSMInvertedIndexComponent component = (LSMInvertedIndexComponent) c;
            component.getInvIndex().destroy();
            component.getDeletedKeysBTree().destroy();
        }
        fileManager.deleteDirs();
    }

    @Override
    public void validate() throws HyracksDataException {
        mutableComponent.getInvIndex().validate();
        mutableComponent.getDeletedKeysBTree().validate();
        for (ILSMComponent c : immutableComponents) {
            LSMInvertedIndexComponent component = (LSMInvertedIndexComponent) c;
            component.getInvIndex().validate();
            component.getDeletedKeysBTree().validate();
        }
    }

    @Override
    public IIndexAccessor createAccessor(IModificationOperationCallback modificationCallback,
            ISearchOperationCallback searchCallback) {
        return new LSMInvertedIndexAccessor(this, lsmHarness, fileManager, createOpContext(modificationCallback,
                searchCallback));
    }

    private LSMInvertedIndexOpContext createOpContext(IModificationOperationCallback modificationCallback,
            ISearchOperationCallback searchCallback) {
        return new LSMInvertedIndexOpContext(mutableComponent.getInvIndex(), mutableComponent.getDeletedKeysBTree(),
                modificationCallback, searchCallback);
    }

    @Override
    public IIndexBulkLoader createBulkLoader(float fillFactor, boolean verifyInput) throws IndexException {
        return new LSMInvertedIndexBulkLoader(fillFactor, verifyInput);
    }

    /**
     * The keys in the in-memory deleted-keys BTree only refer to on-disk components.
     * We delete documents from the in-memory inverted index by deleting its entries directly,
     * while still adding the deleted key to the deleted-keys BTree.
     * Otherwise, inserts would have to remove keys from the in-memory deleted-keys BTree which
     * may cause incorrect behavior (lost deletes) in the following pathological case:
     * Insert doc 1, flush, delete doc 1, insert doc 1
     * After the sequence above doc 1 will now appear twice because the delete of the on-disk doc 1 has been lost.
     * Insert:
     * - Insert document into in-memory inverted index.
     * Delete:
     * - Delete document from in-memory inverted index (ignore if it does not exist).
     * - Insert key into deleted-keys BTree.
     */
    @Override
    public void insertUpdateOrDelete(ITupleReference tuple, IIndexOperationContext ictx) throws HyracksDataException,
            IndexException {
        LSMInvertedIndexOpContext ctx = (LSMInvertedIndexOpContext) ictx;
        ctx.modificationCallback.before(tuple);
        switch (ctx.getOperation()) {
            case INSERT: {
                // Insert into the in-memory inverted index.                
                ctx.memInvIndexAccessor.insert(tuple);
                break;
            }
            case DELETE: {
                ctx.modificationCallback.before(tuple);
                // First remove all entries in the in-memory inverted index (if any).
                ctx.memInvIndexAccessor.delete(tuple);
                // Insert key into the deleted-keys BTree.
                ctx.keysOnlyTuple.reset(tuple);
                try {
                    ctx.deletedKeysBTreeAccessor.insert(ctx.keysOnlyTuple);
                } catch (BTreeDuplicateKeyException e) {
                    // Key has already been deleted.
                }
                break;
            }
            default: {
                throw new UnsupportedOperationException("Operation " + ctx.getOperation() + " not supported.");
            }
        }
    }

    @Override
    public void search(IIndexCursor cursor, List<ILSMComponent> immutableComponents, ISearchPredicate pred,
            IIndexOperationContext ictx, boolean includeMutableComponent) throws HyracksDataException, IndexException {
        int numComponents = (includeMutableComponent) ? immutableComponents.size() : immutableComponents.size() + 1;
        ArrayList<IIndexAccessor> indexAccessors = new ArrayList<IIndexAccessor>(numComponents);
        ArrayList<IIndexAccessor> deletedKeysBTreeAccessors = new ArrayList<IIndexAccessor>(numComponents);
        if (includeMutableComponent) {
            IIndexAccessor invIndexAccessor = mutableComponent.getInvIndex().createAccessor(
                    NoOpOperationCallback.INSTANCE, NoOpOperationCallback.INSTANCE);
            indexAccessors.add(invIndexAccessor);
            IIndexAccessor deletedKeysAccessor = mutableComponent.getDeletedKeysBTree().createAccessor(
                    NoOpOperationCallback.INSTANCE, NoOpOperationCallback.INSTANCE);
            deletedKeysBTreeAccessors.add(deletedKeysAccessor);
        }
        for (int i = 0; i < immutableComponents.size(); i++) {
            LSMInvertedIndexComponent component = (LSMInvertedIndexComponent) immutableComponents.get(i);
            IIndexAccessor invIndexAccessor = component.getInvIndex().createAccessor(NoOpOperationCallback.INSTANCE,
                    NoOpOperationCallback.INSTANCE);
            indexAccessors.add(invIndexAccessor);
            IIndexAccessor deletedKeysAccessor = component.getDeletedKeysBTree().createAccessor(
                    NoOpOperationCallback.INSTANCE, NoOpOperationCallback.INSTANCE);
            deletedKeysBTreeAccessors.add(deletedKeysAccessor);
        }

        ICursorInitialState initState = createCursorInitialState(pred, ictx, includeMutableComponent, indexAccessors,
                deletedKeysBTreeAccessors);
        cursor.open(initState, pred);
    }

    private ICursorInitialState createCursorInitialState(ISearchPredicate pred, IIndexOperationContext ictx,
            boolean includeMutableComponent, ArrayList<IIndexAccessor> indexAccessors,
            ArrayList<IIndexAccessor> deletedKeysBTreeAccessors) {
        ICursorInitialState initState = null;
        PermutingTupleReference keysOnlyTuple = createKeysOnlyTupleReference();
        MultiComparator keyCmp = MultiComparator.createIgnoreFieldLength(invListCmpFactories);
        List<ILSMComponent> operationalComponents = new ArrayList<ILSMComponent>();
        if (includeMutableComponent) {
            operationalComponents.add(getMutableComponent());
        }
        operationalComponents.addAll(immutableComponents);

        // TODO: This check is not pretty, but it does the job. Come up with something more OO in the future.
        // Distinguish between regular searches and range searches (mostly used in merges).
        if (pred instanceof InvertedIndexSearchPredicate) {
            initState = new LSMInvertedIndexSearchCursorInitialState(keyCmp, keysOnlyTuple, indexAccessors,
                    deletedKeysBTreeAccessors, ictx, includeMutableComponent, lsmHarness, operationalComponents);
        } else {
            InMemoryInvertedIndex memInvIndex = (InMemoryInvertedIndex) mutableComponent.getInvIndex();
            MultiComparator tokensAndKeysCmp = MultiComparator.create(memInvIndex.getBTree().getComparatorFactories());
            initState = new LSMInvertedIndexRangeSearchCursorInitialState(tokensAndKeysCmp, keyCmp, keysOnlyTuple,
                    includeMutableComponent, lsmHarness, indexAccessors, deletedKeysBTreeAccessors, pred,
                    operationalComponents);
        }
        return initState;
    }

    /**
     * Returns a permuting tuple reference that projects away the document field(s) of a tuple, only leaving the key fields.
     */
    private PermutingTupleReference createKeysOnlyTupleReference() {
        // Project away token fields.
        int[] keyFieldPermutation = new int[invListTypeTraits.length];
        int numTokenFields = tokenTypeTraits.length;
        for (int i = 0; i < invListTypeTraits.length; i++) {
            keyFieldPermutation[i] = numTokenFields + i;
        }
        return new PermutingTupleReference(keyFieldPermutation);
    }

    @Override
    public ILSMComponent merge(List<ILSMComponent> mergedComponents, ILSMIOOperation operation)
            throws HyracksDataException, IndexException {
        LSMInvertedIndexMergeOperation mergeOp = (LSMInvertedIndexMergeOperation) operation;

        // Create an inverted index instance.
        LSMInvertedIndexComponent component = createDiskInvIndexComponent(componentFactory,
                mergeOp.getDictBTreeMergeTarget(), mergeOp.getDeletedKeysBTreeMergeTarget(), true);

        IInvertedIndex mergedDiskInvertedIndex = component.getInvIndex();
        IIndexCursor cursor = mergeOp.getCursor();
        IIndexBulkLoader invIndexBulkLoader = mergedDiskInvertedIndex.createBulkLoader(1.0f, true);
        try {
            while (cursor.hasNext()) {
                cursor.next();
                ITupleReference tuple = cursor.getTuple();
                invIndexBulkLoader.add(tuple);
            }
        } finally {
            cursor.close();
        }
        invIndexBulkLoader.end();

        // Create an empty deleted keys BTree (do nothing with the returned index).
        BTree deletedKeysBTree = component.getDeletedKeysBTree();

        // Add the merged components for cleanup.
        mergedComponents.addAll(mergeOp.getMergingComponents());

        return new LSMInvertedIndexComponent(mergedDiskInvertedIndex, deletedKeysBTree);
    }

    @Override
    public ILSMIOOperation createMergeOperation(ILSMIOOperationCallback callback) throws HyracksDataException,
            IndexException {
        LSMInvertedIndexOpContext ctx = createOpContext(NoOpOperationCallback.INSTANCE, NoOpOperationCallback.INSTANCE);
        ctx.setOperation(IndexOperation.MERGE);
        IIndexCursor cursor = new LSMInvertedIndexRangeSearchCursor(ctx);
        RangePredicate mergePred = new RangePredicate(null, null, true, true, null, null);

        // Scan diskInvertedIndexes ignoring the memoryInvertedIndex.
        List<ILSMComponent> mergingComponents = lsmHarness.search(cursor, mergePred, ctx, false);
        if (mergingComponents.size() <= 1) {
            cursor.close();
            return null;
        }

        LSMInvertedIndexComponent firstComponent = (LSMInvertedIndexComponent) mergingComponents.get(0);
        OnDiskInvertedIndex firstInvIndex = (OnDiskInvertedIndex) firstComponent.getInvIndex();
        String firstFileName = firstInvIndex.getBTree().getFileReference().getFile().getName();

        LSMInvertedIndexComponent lastComponent = (LSMInvertedIndexComponent) mergingComponents.get(mergingComponents
                .size() - 1);
        OnDiskInvertedIndex lastInvIndex = (OnDiskInvertedIndex) lastComponent.getInvIndex();
        String lastFileName = lastInvIndex.getBTree().getFileReference().getFile().getName();

        LSMComponentFileReferences relMergeFileRefs = fileManager.getRelMergeFileReference(firstFileName, lastFileName);
        LSMInvertedIndexMergeOperation mergeOp = new LSMInvertedIndexMergeOperation(
                (ILSMIndexAccessorInternal) createAccessor(null, null), mergingComponents, cursor,
                relMergeFileRefs.getInsertIndexFileReference(), relMergeFileRefs.getDeleteIndexFileReference(),
                callback);

        return mergeOp;
    }

    @Override
    public ILSMComponent flush(ILSMIOOperation operation) throws HyracksDataException, IndexException {
        LSMInvertedIndexFlushOperation flushOp = (LSMInvertedIndexFlushOperation) operation;

        // Create an inverted index instance to be bulk loaded.
        LSMInvertedIndexComponent component = createDiskInvIndexComponent(componentFactory,
                flushOp.getDictBTreeFlushTarget(), flushOp.getDeletedKeysBTreeFlushTarget(), true);
        IInvertedIndex diskInvertedIndex = component.getInvIndex();

        // Create a scan cursor on the BTree underlying the in-memory inverted index.
        InMemoryInvertedIndexAccessor memInvIndexAccessor = (InMemoryInvertedIndexAccessor) mutableComponent
                .getInvIndex().createAccessor(NoOpOperationCallback.INSTANCE, NoOpOperationCallback.INSTANCE);
        BTreeAccessor memBTreeAccessor = memInvIndexAccessor.getBTreeAccessor();
        RangePredicate nullPred = new RangePredicate(null, null, true, true, null, null);
        IIndexCursor scanCursor = memBTreeAccessor.createSearchCursor();
        memBTreeAccessor.search(scanCursor, nullPred);

        // Bulk load the disk inverted index from the in-memory inverted index.
        IIndexBulkLoader invIndexBulkLoader = diskInvertedIndex.createBulkLoader(1.0f, false);
        try {
            while (scanCursor.hasNext()) {
                scanCursor.next();
                invIndexBulkLoader.add(scanCursor.getTuple());
            }
        } finally {
            scanCursor.close();
        }
        invIndexBulkLoader.end();

        // Create an BTree instance for the deleted keys.
        BTree diskDeletedKeysBTree = component.getDeletedKeysBTree();

        // Create a scan cursor on the deleted keys BTree underlying the in-memory inverted index.
        IIndexAccessor deletedKeysBTreeAccessor = mutableComponent.getDeletedKeysBTree().createAccessor(
                NoOpOperationCallback.INSTANCE, NoOpOperationCallback.INSTANCE);
        IIndexCursor deletedKeysScanCursor = deletedKeysBTreeAccessor.createSearchCursor();
        deletedKeysBTreeAccessor.search(deletedKeysScanCursor, nullPred);

        // Bulk load the deleted-keys BTree.
        IIndexBulkLoader deletedKeysBTreeBulkLoader = diskDeletedKeysBTree.createBulkLoader(1.0f, false);
        try {
            while (deletedKeysScanCursor.hasNext()) {
                deletedKeysScanCursor.next();
                deletedKeysBTreeBulkLoader.add(deletedKeysScanCursor.getTuple());
            }
        } finally {
            deletedKeysScanCursor.close();
        }
        deletedKeysBTreeBulkLoader.end();

        return new LSMInvertedIndexComponent(diskInvertedIndex, diskDeletedKeysBTree);
    }

    private ILSMComponent createBulkLoadTarget() throws HyracksDataException, IndexException {
        LSMComponentFileReferences componentFileRefs = fileManager.getRelFlushFileReference();
        return createDiskInvIndexComponent(componentFactory, componentFileRefs.getInsertIndexFileReference(),
                componentFileRefs.getDeleteIndexFileReference(), true);
    }

    public class LSMInvertedIndexBulkLoader implements IIndexBulkLoader {
        private final ILSMComponent component;
        private final IIndexBulkLoader invIndexBulkLoader;

        public LSMInvertedIndexBulkLoader(float fillFactor, boolean verifyInput) throws IndexException {
            // Note that by using a flush target file name, we state that the
            // new bulk loaded tree is "newer" than any other merged tree.
            try {
                component = createBulkLoadTarget();
            } catch (HyracksDataException e) {
                throw new TreeIndexException(e);
            } catch (IndexException e) {
                throw new TreeIndexException(e);
            }
            invIndexBulkLoader = ((LSMInvertedIndexComponent) component).getInvIndex().createBulkLoader(fillFactor,
                    verifyInput);
        }

        @Override
        public void add(ITupleReference tuple) throws IndexException, HyracksDataException {
            try {
                invIndexBulkLoader.add(tuple);
            } catch (IndexException e) {
                handleException();
                throw e;
            } catch (HyracksDataException e) {
                handleException();
                throw e;
            } catch (RuntimeException e) {
                handleException();
                throw e;
            }
        }

        protected void handleException() throws HyracksDataException {
            ((LSMInvertedIndexComponent) component).getInvIndex().deactivate();
            ((LSMInvertedIndexComponent) component).getInvIndex().destroy();
            ((LSMInvertedIndexComponent) component).getDeletedKeysBTree().deactivate();
            ((LSMInvertedIndexComponent) component).getDeletedKeysBTree().destroy();
        }

        @Override
        public void end() throws IndexException, HyracksDataException {
            invIndexBulkLoader.end();
            lsmHarness.addBulkLoadedComponent(component);
        }
    }

    @Override
    public void resetMutableComponent() throws HyracksDataException {
        memFreePageManager.reset();
        mutableComponent.getInvIndex().clear();
        mutableComponent.getDeletedKeysBTree().clear();
    }

    @Override
    public long getMemoryAllocationSize() {
        InMemoryBufferCache memBufferCache = (InMemoryBufferCache) mutableComponent.getInvIndex().getBufferCache();
        return memBufferCache.getNumPages() * memBufferCache.getPageSize();
    }

    @Override
    public IInvertedListCursor createInvertedListCursor() {
        throw new UnsupportedOperationException("Cannot create inverted list cursor on lsm inverted index.");
    }

    @Override
    public void openInvertedListCursor(IInvertedListCursor listCursor, ITupleReference searchKey,
            IIndexOperationContext ictx) throws HyracksDataException, IndexException {
        throw new UnsupportedOperationException("Cannot open inverted list cursor on lsm inverted index.");
    }

    @Override
    public ITypeTraits[] getInvListTypeTraits() {
        return invListTypeTraits;
    }

    @Override
    public IBinaryComparatorFactory[] getInvListCmpFactories() {
        return invListCmpFactories;
    }

    @Override
    public ITypeTraits[] getTokenTypeTraits() {
        return tokenTypeTraits;
    }

    @Override
    public IBinaryComparatorFactory[] getTokenCmpFactories() {
        return tokenCmpFactories;
    }

    public IBinaryTokenizerFactory getTokenizerFactory() {
        return tokenizerFactory;
    }

    @Override
    public void markAsValid(ILSMComponent lsmComponent) throws HyracksDataException {
        LSMInvertedIndexComponent invIndexComponent = (LSMInvertedIndexComponent) lsmComponent;
        OnDiskInvertedIndex invIndex = (OnDiskInvertedIndex) invIndexComponent.getInvIndex();
        ITreeIndex treeIndex = invIndex.getBTree();
        // Flush inverted index first.
        forceFlushDirtyPages(treeIndex);
        forceFlushInvListsFileDirtyPages(invIndex);
        // Flush deleted keys BTree.
        forceFlushDirtyPages(invIndexComponent.getDeletedKeysBTree());
        // We use the dictionary BTree for marking the inverted index as valid.
        markAsValidInternal(treeIndex);
    }

    protected void forceFlushInvListsFileDirtyPages(OnDiskInvertedIndex invIndex) throws HyracksDataException {
        int fileId = invIndex.getInvListsFileId();
        IBufferCache bufferCache = invIndex.getBufferCache();
        int startPageId = 0;
        int maxPageId = invIndex.getInvListsMaxPageId();
        forceFlushDirtyPages(bufferCache, fileId, startPageId, maxPageId);
    }

    @Override
    public ILSMComponent getMutableComponent() {
        return mutableComponent;
    }
}

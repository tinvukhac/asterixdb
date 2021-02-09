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
package edu.uci.ics.asterix.hyracks.bootstrap;

import java.util.List;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

import edu.uci.ics.asterix.common.config.DatasetConfig.DatasetType;
import edu.uci.ics.asterix.common.config.DatasetConfig.ExternalDatasetTransactionState;
import edu.uci.ics.asterix.common.config.DatasetConfig.ExternalFilePendingOp;
import edu.uci.ics.asterix.file.ExternalIndexingOperations;
import edu.uci.ics.asterix.metadata.MetadataManager;
import edu.uci.ics.asterix.metadata.MetadataTransactionContext;
import edu.uci.ics.asterix.metadata.api.IClusterEventsSubscriber;
import edu.uci.ics.asterix.metadata.api.IClusterManagementWork;
import edu.uci.ics.asterix.metadata.bootstrap.MetadataConstants;
import edu.uci.ics.asterix.metadata.cluster.IClusterManagementWorkResponse;
import edu.uci.ics.asterix.metadata.declared.AqlMetadataProvider;
import edu.uci.ics.asterix.metadata.entities.Dataset;
import edu.uci.ics.asterix.metadata.entities.Dataverse;
import edu.uci.ics.asterix.metadata.entities.ExternalDatasetDetails;
import edu.uci.ics.asterix.metadata.entities.ExternalFile;
import edu.uci.ics.asterix.metadata.entities.Index;
import edu.uci.ics.asterix.om.util.AsterixClusterProperties;
import edu.uci.ics.asterix.om.util.AsterixClusterProperties.State;
import edu.uci.ics.hyracks.api.client.HyracksConnection;
import edu.uci.ics.hyracks.api.job.JobId;
import edu.uci.ics.hyracks.api.job.JobSpecification;

public class AsterixGlobalRecoveryManager implements IClusterEventsSubscriber {

    private static State state;
    private static final Logger LOGGER = Logger.getLogger(AsterixGlobalRecoveryManager.class.getName());
    private HyracksConnection hcc;
    public static AsterixGlobalRecoveryManager INSTANCE;

    public AsterixGlobalRecoveryManager(HyracksConnection hcc) throws Exception {
        state = AsterixClusterProperties.INSTANCE.getState();
        this.hcc = hcc;
    }

    @Override
    public Set<IClusterManagementWork> notifyNodeFailure(Set<String> deadNodeIds) {
        state = AsterixClusterProperties.INSTANCE.getState();
        AsterixClusterProperties.INSTANCE.setGlobalRecoveryCompleted(false);
        return null;
    }

    @Override
    public Set<IClusterManagementWork> notifyNodeJoin(String joinedNodeId) {
        // perform global recovery if state changed to active
        final State newState = AsterixClusterProperties.INSTANCE.getState();
        boolean needToRecover = !newState.equals(state) && (newState == State.ACTIVE);
        if (needToRecover) {
            Thread recoveryThread = new Thread(new Runnable() {
                @Override
                public void run() {
                    LOGGER.info("Starting AsterixDB's Global Recovery");
                    MetadataTransactionContext mdTxnCtx = null;
                    try {
                        Thread.sleep(4000);
                        MetadataManager.INSTANCE.init();
                        // Loop over datasets
                        mdTxnCtx = MetadataManager.INSTANCE.beginTransaction();
                        List<Dataverse> dataverses = MetadataManager.INSTANCE.getDataverses(mdTxnCtx);
                        for (Dataverse dataverse : dataverses) {
                            if (!dataverse.getDataverseName().equals(MetadataConstants.METADATA_DATAVERSE_NAME)) {
                                AqlMetadataProvider metadataProvider = new AqlMetadataProvider(dataverse);
                                List<Dataset> datasets = MetadataManager.INSTANCE.getDataverseDatasets(mdTxnCtx,
                                        dataverse.getDataverseName());
                                for (Dataset dataset : datasets) {
                                    if (dataset.getDatasetType() == DatasetType.EXTERNAL) {
                                        // External dataset
                                        // Get indexes
                                        List<Index> indexes = MetadataManager.INSTANCE.getDatasetIndexes(mdTxnCtx,
                                                dataset.getDataverseName(), dataset.getDatasetName());
                                        if (indexes.size() > 0) {
                                            // Get the state of the dataset
                                            ExternalDatasetDetails dsd = (ExternalDatasetDetails) dataset
                                                    .getDatasetDetails();
                                            ExternalDatasetTransactionState datasetState = dsd.getState();
                                            if (datasetState == ExternalDatasetTransactionState.BEGIN) {
                                                List<ExternalFile> files = MetadataManager.INSTANCE
                                                        .getDatasetExternalFiles(mdTxnCtx, dataset);
                                                // if persumed abort, roll backward
                                                // 1. delete all pending files
                                                for (ExternalFile file : files) {
                                                    if (file.getPendingOp() != ExternalFilePendingOp.PENDING_NO_OP) {
                                                        MetadataManager.INSTANCE.dropExternalFile(mdTxnCtx, file);
                                                    }
                                                }
                                                // 2. clean artifacts in NCs
                                                metadataProvider.setMetadataTxnContext(mdTxnCtx);
                                                JobSpecification jobSpec = ExternalIndexingOperations.buildAbortOp(
                                                        dataset, indexes, metadataProvider);
                                                executeHyracksJob(jobSpec);
                                                // 3. correct the dataset state
                                                ((ExternalDatasetDetails) dataset.getDatasetDetails())
                                                        .setState(ExternalDatasetTransactionState.COMMIT);
                                                MetadataManager.INSTANCE.updateDataset(mdTxnCtx, dataset);
                                                MetadataManager.INSTANCE.commitTransaction(mdTxnCtx);
                                                mdTxnCtx = MetadataManager.INSTANCE.beginTransaction();
                                            } else if (datasetState == ExternalDatasetTransactionState.READY_TO_COMMIT) {
                                                List<ExternalFile> files = MetadataManager.INSTANCE
                                                        .getDatasetExternalFiles(mdTxnCtx, dataset);
                                                // if ready to commit, roll forward
                                                // 1. commit indexes in NCs
                                                metadataProvider.setMetadataTxnContext(mdTxnCtx);
                                                JobSpecification jobSpec = ExternalIndexingOperations.buildRecoverOp(
                                                        dataset, indexes, metadataProvider);
                                                executeHyracksJob(jobSpec);
                                                // 2. add pending files in metadata
                                                for (ExternalFile file : files) {
                                                    if (file.getPendingOp() == ExternalFilePendingOp.PENDING_ADD_OP) {
                                                        MetadataManager.INSTANCE.dropExternalFile(mdTxnCtx, file);
                                                        file.setPendingOp(ExternalFilePendingOp.PENDING_NO_OP);
                                                        MetadataManager.INSTANCE.addExternalFile(mdTxnCtx, file);
                                                    } else if (file.getPendingOp() == ExternalFilePendingOp.PENDING_DROP_OP) {
                                                        // find original file
                                                        for (ExternalFile originalFile : files) {
                                                            if (originalFile.getFileName().equals(file.getFileName())) {
                                                                MetadataManager.INSTANCE.dropExternalFile(mdTxnCtx,
                                                                        file);
                                                                MetadataManager.INSTANCE.dropExternalFile(mdTxnCtx,
                                                                        originalFile);
                                                                break;
                                                            }
                                                        }
                                                    } else if (file.getPendingOp() == ExternalFilePendingOp.PENDING_APPEND_OP) {
                                                        // find original file
                                                        for (ExternalFile originalFile : files) {
                                                            if (originalFile.getFileName().equals(file.getFileName())) {
                                                                MetadataManager.INSTANCE.dropExternalFile(mdTxnCtx,
                                                                        file);
                                                                MetadataManager.INSTANCE.dropExternalFile(mdTxnCtx,
                                                                        originalFile);
                                                                originalFile.setSize(file.getSize());
                                                                MetadataManager.INSTANCE.addExternalFile(mdTxnCtx,
                                                                        originalFile);
                                                            }
                                                        }
                                                    }
                                                }
                                                // 3. correct the dataset state
                                                ((ExternalDatasetDetails) dataset.getDatasetDetails())
                                                        .setState(ExternalDatasetTransactionState.COMMIT);
                                                MetadataManager.INSTANCE.updateDataset(mdTxnCtx, dataset);
                                                MetadataManager.INSTANCE.commitTransaction(mdTxnCtx);
                                                mdTxnCtx = MetadataManager.INSTANCE.beginTransaction();
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        MetadataManager.INSTANCE.commitTransaction(mdTxnCtx);
                    } catch (Exception e) {
                        // This needs to be fixed <-- Needs to shutdown the system -->
                        /*
                         * Note: Throwing this illegal state exception will terminate this thread
                         * and feeds listeners will not be notified.
                         */
                        LOGGER.severe("Global recovery was not completed successfully" + e);
                        try {
                            MetadataManager.INSTANCE.abortTransaction(mdTxnCtx);
                        } catch (Exception e1) {
                            if (LOGGER.isLoggable(Level.SEVERE)) {
                                LOGGER.severe("Exception in aborting" + e.getMessage());
                            }
                            throw new IllegalStateException(e1);
                        }
                    }
                    AsterixClusterProperties.INSTANCE.setGlobalRecoveryCompleted(true);
                    LOGGER.info("Global Recovery Completed");
                }
            });
            state = newState;
            recoveryThread.start();
        }
        return null;
    }

    private void executeHyracksJob(JobSpecification spec) throws Exception {
        spec.setMaxReattempts(0);
        JobId jobId = hcc.startJob(spec);
        hcc.waitForCompletion(jobId);
    }

    @Override
    public void notifyRequestCompletion(IClusterManagementWorkResponse response) {
        // Do nothing
    }

    @Override
    public void notifyStateChange(State previousState, State newState) {
        // Do nothing?
    }
}

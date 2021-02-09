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
package edu.uci.ics.asterix.api.common;

import java.io.File;
import java.util.EnumSet;

import edu.uci.ics.asterix.common.config.GlobalConfig;
import edu.uci.ics.asterix.hyracks.bootstrap.CCApplicationEntryPoint;
import edu.uci.ics.asterix.hyracks.bootstrap.NCApplicationEntryPoint;
import edu.uci.ics.hyracks.api.client.HyracksConnection;
import edu.uci.ics.hyracks.api.client.IHyracksClientConnection;
import edu.uci.ics.hyracks.api.job.JobFlag;
import edu.uci.ics.hyracks.api.job.JobId;
import edu.uci.ics.hyracks.api.job.JobSpecification;
import edu.uci.ics.hyracks.control.cc.ClusterControllerService;
import edu.uci.ics.hyracks.control.common.controllers.CCConfig;
import edu.uci.ics.hyracks.control.common.controllers.NCConfig;
import edu.uci.ics.hyracks.control.nc.NodeControllerService;

public class AsterixHyracksIntegrationUtil {

    public static final String[] NC_IDS = { "nc1", "nc2" };
    public static final String[] ASTERIX_DATA_DIRS = new String[] { "nc1data", "nc2data" };

    public static final int DEFAULT_HYRACKS_CC_CLIENT_PORT = 1098;

    public static final int DEFAULT_HYRACKS_CC_CLUSTER_PORT = 1099;

    private static ClusterControllerService cc;
    private static NodeControllerService nc1;
    private static NodeControllerService nc2;
    private static IHyracksClientConnection hcc;

    public static void init() throws Exception {
        CCConfig ccConfig = new CCConfig();
        ccConfig.clusterNetIpAddress = "127.0.0.1";
        ccConfig.clientNetIpAddress = "127.0.0.1";
        ccConfig.clientNetPort = DEFAULT_HYRACKS_CC_CLIENT_PORT;
        ccConfig.clusterNetPort = DEFAULT_HYRACKS_CC_CLUSTER_PORT;
        ccConfig.defaultMaxJobAttempts = 0;
        ccConfig.resultTTL = 30000;
        ccConfig.resultSweepThreshold = 1000;
        ccConfig.appCCMainClass = CCApplicationEntryPoint.class.getName();
        // ccConfig.useJOL = true;
        cc = new ClusterControllerService(ccConfig);
        cc.start();

        NCConfig ncConfig1 = new NCConfig();
        ncConfig1.ccHost = "localhost";
        ncConfig1.ccPort = DEFAULT_HYRACKS_CC_CLUSTER_PORT;
        ncConfig1.clusterNetIPAddress = "127.0.0.1";
        ncConfig1.dataIPAddress = "127.0.0.1";
        ncConfig1.datasetIPAddress = "127.0.0.1";
        ncConfig1.nodeId = NC_IDS[0];
        ncConfig1.resultTTL = 30000;
        ncConfig1.resultSweepThreshold = 1000;
        ncConfig1.ioDevices = System.getProperty("java.io.tmpdir") + File.separator + "nc1/iodevice0" + ","
                + System.getProperty("java.io.tmpdir") + File.separator + "nc1/iodevice1";
        ncConfig1.appNCMainClass = NCApplicationEntryPoint.class.getName();
        nc1 = new NodeControllerService(ncConfig1);
        nc1.start();

        NCConfig ncConfig2 = new NCConfig();
        ncConfig2.ccHost = "localhost";
        ncConfig2.ccPort = DEFAULT_HYRACKS_CC_CLUSTER_PORT;
        ncConfig2.clusterNetIPAddress = "127.0.0.1";
        ncConfig2.dataIPAddress = "127.0.0.1";
        ncConfig2.datasetIPAddress = "127.0.0.1";
        ncConfig2.nodeId = NC_IDS[1];
        ncConfig2.resultTTL = 30000;
        ncConfig2.resultSweepThreshold = 1000;
        ncConfig2.ioDevices = System.getProperty("java.io.tmpdir") + File.separator + "nc2/iodevice0" + ","
                + System.getProperty("java.io.tmpdir") + File.separator + "nc2/iodevice1";
        ncConfig2.appNCMainClass = NCApplicationEntryPoint.class.getName();
        nc2 = new NodeControllerService(ncConfig2);
        nc2.start();

        hcc = new HyracksConnection(cc.getConfig().clientNetIpAddress, cc.getConfig().clientNetPort);
    }

    public static IHyracksClientConnection getHyracksClientConnection() {
        return hcc;
    }

    public static void deinit() throws Exception {
        if (nc2 != null) nc2.stop();
        if (nc1 != null) nc1.stop();
        if (cc != null) cc.stop();
    }

    public static void runJob(JobSpecification spec) throws Exception {
        GlobalConfig.ASTERIX_LOGGER.info(spec.toJSON().toString());
        JobId jobId = hcc.startJob(spec, EnumSet.of(JobFlag.PROFILE_RUNTIME));
        GlobalConfig.ASTERIX_LOGGER.info(jobId.toString());
        hcc.waitForCompletion(jobId);
    }

    /**
     * main method to run a simple 2 node cluster in-process
     *
     * suggested VM arguments:
     * <code>-enableassertions -Xmx2048m -Dfile.encoding=UTF-8</code>
     *
     * @param args unused
     */
    public static void main(String[] args) {
        Runtime.getRuntime().addShutdownHook(new Thread() {
            public void run() {
                try {
                    deinit();
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        });
        try {
            System.setProperty(GlobalConfig.CONFIG_FILE_PROPERTY, "asterix-build-configuration.xml");

            init();
            while (true) {
                Thread.sleep(10000);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}

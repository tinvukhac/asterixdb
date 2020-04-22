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
package org.apache.asterix.test.external_dataset.aws;

import static org.apache.hyracks.util.file.FileUtil.joinPath;

import java.io.File;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.URI;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.asterix.common.api.INcApplicationContext;
import org.apache.asterix.test.common.TestExecutor;
import org.apache.asterix.test.runtime.ExecutionTestUtil;
import org.apache.asterix.test.runtime.LangExecutionUtil;
import org.apache.asterix.testframework.context.TestCaseContext;
import org.apache.asterix.testframework.context.TestFileContext;
import org.apache.asterix.testframework.xml.TestCase;
import org.apache.commons.io.FilenameUtils;
import org.apache.commons.lang3.mutable.MutableInt;
import org.apache.hyracks.control.nc.NodeControllerService;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.MethodSorters;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import io.findify.s3mock.S3Mock;
import software.amazon.awssdk.auth.credentials.AnonymousCredentialsProvider;
import software.amazon.awssdk.core.sync.RequestBody;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.services.s3.S3Client;
import software.amazon.awssdk.services.s3.S3ClientBuilder;
import software.amazon.awssdk.services.s3.model.CreateBucketRequest;
import software.amazon.awssdk.services.s3.model.DeleteBucketRequest;
import software.amazon.awssdk.services.s3.model.NoSuchBucketException;
import software.amazon.awssdk.services.s3.model.PutObjectRequest;

/**
 * Runs an AWS S3 mock server and test it as an external dataset
 */
@RunWith(Parameterized.class)
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class AwsS3ExternalDatasetTest {

    private static final Logger LOGGER = LogManager.getLogger();

    protected static String TEST_CONFIG_FILE_NAME;
    static Runnable PREPARE_S3_BUCKET;

    // S3 mock server
    private static S3Mock s3MockServer;

    // IMPORTANT: The following values must be used in the AWS S3 test case
    private static S3Client client;
    private static final String S3_MOCK_SERVER_BUCKET = "playground";
    private static final String S3_MOCK_SERVER_BUCKET_DEFINITION = "json-data/reviews/"; // data resides here
    private static final String S3_MOCK_SERVER_BUCKET_CSV_DEFINITION = "csv-data/reviews/"; // data resides here
    private static final String S3_MOCK_SERVER_BUCKET_TSV_DEFINITION = "tsv-data/reviews/"; // data resides here
    private static final String S3_MOCK_SERVER_REGION = "us-west-2";
    private static final int S3_MOCK_SERVER_PORT = 8001;
    private static final String S3_MOCK_SERVER_HOSTNAME = "http://localhost:" + S3_MOCK_SERVER_PORT;
    private static final String CSV_DATA_PATH = joinPath("data", "csv");
    private static final String TSV_DATA_PATH = joinPath("data", "tsv");
    private static final Set<String> fileNames = new HashSet<>();
    private static final CreateBucketRequest.Builder CREATE_BUCKET_BUILDER = CreateBucketRequest.builder();
    private static final DeleteBucketRequest.Builder DELETE_BUCKET_BUILDER = DeleteBucketRequest.builder();
    private static final PutObjectRequest.Builder PUT_OBJECT_BUILDER = PutObjectRequest.builder();

    @BeforeClass
    public static void setUp() throws Exception {
        final TestExecutor testExecutor = new AwsTestExecutor();
        LangExecutionUtil.setUp(TEST_CONFIG_FILE_NAME, testExecutor);
        setNcEndpoints(testExecutor);
        startAwsS3MockServer();
    }

    @AfterClass
    public static void tearDown() throws Exception {
        LangExecutionUtil.tearDown();

        // Shutting down S3 mock server
        LOGGER.info("Shutting down S3 mock server and client");
        if (client != null) {
            client.close();
        }
        if (s3MockServer != null) {
            s3MockServer.shutdown();
        }
        LOGGER.info("S3 mock down and client shut down successfully");
    }

    @Parameters(name = "SqlppExecutionTest {index}: {0}")
    public static Collection<Object[]> tests() throws Exception {
        TEST_CONFIG_FILE_NAME = "src/main/resources/cc.conf";
        PREPARE_S3_BUCKET = AwsS3ExternalDatasetTest::prepareS3Bucket;
        return LangExecutionUtil.tests("only_external_dataset.xml", "testsuite_external_dataset.xml");
    }

    protected TestCaseContext tcCtx;

    public AwsS3ExternalDatasetTest(TestCaseContext tcCtx) {
        this.tcCtx = tcCtx;
    }

    @Test
    public void test() throws Exception {
        LangExecutionUtil.test(tcCtx);
    }

    private static void setNcEndpoints(TestExecutor testExecutor) {
        final NodeControllerService[] ncs = ExecutionTestUtil.integrationUtil.ncs;
        final Map<String, InetSocketAddress> ncEndPoints = new HashMap<>();
        final String ip = InetAddress.getLoopbackAddress().getHostAddress();
        for (NodeControllerService nc : ncs) {
            final String nodeId = nc.getId();
            final INcApplicationContext appCtx = (INcApplicationContext) nc.getApplicationContext();
            int apiPort = appCtx.getExternalProperties().getNcApiPort();
            ncEndPoints.put(nodeId, InetSocketAddress.createUnresolved(ip, apiPort));
        }
        testExecutor.setNcEndPoints(ncEndPoints);
    }

    /**
     * Starts the AWS s3 mocking server and loads some files for testing
     */
    private static void startAwsS3MockServer() {
        // Starting S3 mock server to be used instead of real S3 server
        LOGGER.info("Starting S3 mock server");
        s3MockServer = new S3Mock.Builder().withPort(S3_MOCK_SERVER_PORT).withInMemoryBackend().build();
        s3MockServer.start();
        LOGGER.info("S3 mock server started successfully");

        // Create a client and add some files to the S3 mock server
        LOGGER.info("Creating S3 client to load initial files to S3 mock server");
        S3ClientBuilder builder = S3Client.builder();
        URI endpoint = URI.create(S3_MOCK_SERVER_HOSTNAME); // endpoint pointing to S3 mock server
        builder.region(Region.of(S3_MOCK_SERVER_REGION)).credentialsProvider(AnonymousCredentialsProvider.create())
                .endpointOverride(endpoint);
        client = builder.build();
        LOGGER.info("Client created successfully");

        // Create the bucket and upload some json files
        PREPARE_S3_BUCKET.run();
    }

    /**
     * Creates a bucket and fills it with some files for testing purpose.
     */
    private static void prepareS3Bucket() {
        LOGGER.info("creating bucket " + S3_MOCK_SERVER_BUCKET);
        client.createBucket(CreateBucketRequest.builder().bucket(S3_MOCK_SERVER_BUCKET).build());
        LOGGER.info("bucket created successfully");

        LOGGER.info("Adding JSON files to the bucket");
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "0.json").build(),
                RequestBody.fromString("{\"id\": 1, \"year\": null, \"quarter\": null, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "1.json").build(),
                RequestBody.fromString("{\"id\": 2, \"year\": null, \"quarter\": null, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2018/1.json").build(),
                RequestBody.fromString("{\"id\": 3, \"year\": 2018, \"quarter\": null, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2018/2.json").build(),
                RequestBody.fromString("{\"id\": 4, \"year\": 2018, \"quarter\": null, \"review\": \"bad\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2018/q1/1.json").build(),
                RequestBody.fromString("{\"id\": 5, \"year\": 2018, \"quarter\": 1, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2018/q1/2.json").build(),
                RequestBody.fromString("{\"id\": 6, \"year\": 2018, \"quarter\": 1, \"review\": \"bad\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2018/q2/1.json").build(),
                RequestBody.fromString("{\"id\": 7, \"year\": 2018, \"quarter\": 2, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2018/q2/2.json").build(),
                RequestBody.fromString("{\"id\": 8, \"year\": 2018, \"quarter\": 2, \"review\": \"bad\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2019/1.json").build(),
                RequestBody.fromString("{\"id\": 9, \"year\": 2019, \"quarter\": null, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2019/2.json").build(),
                RequestBody.fromString("{\"id\": 10, \"year\": 2019, \"quarter\": null, \"review\": \"bad\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2019/q1/1.json").build(),
                RequestBody.fromString("{\"id\": 11, \"year\": 2019, \"quarter\": 1, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2019/q1/2.json").build(),
                RequestBody.fromString("{\"id\": 12, \"year\": 2019, \"quarter\": 1, \"review\": \"bad\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2019/q2/1.json").build(),
                RequestBody.fromString("{\"id\": 13, \"year\": 2019, \"quarter\": 2, \"review\": \"good\"}"));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_DEFINITION + "2019/q2/2.json").build(),
                RequestBody.fromString("{\"id\": 14, \"year\": 2019, \"quarter\": 2, \"review\": \"bad\"}"));

        LOGGER.info("Adding CSV files to the bucket");
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_CSV_DEFINITION + "01.csv").build(),
                RequestBody.fromFile(Paths.get(CSV_DATA_PATH, "01.csv")));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_CSV_DEFINITION + "2018/01.csv").build(),
                RequestBody.fromFile(Paths.get(CSV_DATA_PATH, "02.csv")));

        LOGGER.info("Adding TSV files to the bucket");
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_TSV_DEFINITION + "01.tsv").build(),
                RequestBody.fromFile(Paths.get(TSV_DATA_PATH, "01.tsv")));
        client.putObject(
                PutObjectRequest.builder().bucket(S3_MOCK_SERVER_BUCKET)
                        .key(S3_MOCK_SERVER_BUCKET_TSV_DEFINITION + "2018/01.tsv").build(),
                RequestBody.fromFile(Paths.get(TSV_DATA_PATH, "02.tsv")));
        LOGGER.info("Files added successfully");
    }

    static class AwsTestExecutor extends TestExecutor {

        public void executeTestFile(TestCaseContext testCaseCtx, TestFileContext ctx, Map<String, Object> variableCtx,
                String statement, boolean isDmlRecoveryTest, ProcessBuilder pb, TestCase.CompilationUnit cUnit,
                MutableInt queryCount, List<TestFileContext> expectedResultFileCtxs, File testFile, String actualPath,
                MutableInt actualWarnCount) throws Exception {
            String[] lines;
            switch (ctx.getType()) {
                case "s3bucket":
                    // <bucket_name> <def_name> <file1,file2,file3>
                    lines = TestExecutor.stripAllComments(statement).trim().split("\n");
                    String lastLine = lines[lines.length - 1];
                    String[] command = lastLine.trim().split(" ");
                    int length = command.length;
                    if (length != 3) {
                        throw new Exception("invalid create bucket format");
                    }
                    dropRecreateBucket(command[0], command[1], command[2]);
                    break;
                default:
                    super.executeTestFile(testCaseCtx, ctx, variableCtx, statement, isDmlRecoveryTest, pb, cUnit,
                            queryCount, expectedResultFileCtxs, testFile, actualPath, actualWarnCount);
            }
        }
    }

    private static void dropRecreateBucket(String bucketName, String definition, String files) {
        String definitionPath = definition + (definition.endsWith("/") ? "" : "/");
        String[] fileSplits = files.split(",");

        LOGGER.info("Dropping bucket");
        try {
            client.deleteBucket(DELETE_BUCKET_BUILDER.bucket(bucketName).build());
        } catch (NoSuchBucketException e) {
            // ignore
        }
        LOGGER.info("Creating bucket " + bucketName);
        client.createBucket(CREATE_BUCKET_BUILDER.bucket(bucketName).build());
        LOGGER.info("Uploading to bucket " + bucketName + " definition " + definitionPath);
        fileNames.clear();
        for (int i = 0; i < fileSplits.length; i++) {
            String fileName = FilenameUtils.getName(fileSplits[i]);
            while (fileNames.contains(fileName)) {
                fileName = (i + 1) + fileName;
            }
            fileNames.add(fileName);
            client.putObject(PUT_OBJECT_BUILDER.bucket(bucketName).key(definitionPath + fileName).build(),
                    RequestBody.fromFile(Paths.get(fileSplits[i])));
        }
        LOGGER.info("Done creating bucket with data");
    }
}

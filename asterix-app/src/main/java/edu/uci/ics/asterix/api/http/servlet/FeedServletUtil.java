package edu.uci.ics.asterix.api.http.servlet;

import java.io.IOException;
import java.io.InputStream;
import java.net.Socket;
import java.nio.CharBuffer;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.logging.Level;
import java.util.logging.Logger;

import edu.uci.ics.asterix.common.feeds.FeedConnectionId;
import edu.uci.ics.asterix.hyracks.bootstrap.FeedLifecycleListener;
import edu.uci.ics.asterix.metadata.feeds.RemoteSocketMessageListener;

public class FeedServletUtil {

    private static final Logger LOGGER = Logger.getLogger(FeedServletUtil.class.getName());
    private static final char EOL = (char) "\n".getBytes()[0];

    public static void initiateSubscription(FeedConnectionId feedId, String host, int port) throws IOException {
        LinkedBlockingQueue<String> outbox = new LinkedBlockingQueue<String>();
        int subscriptionPort = port + 1;
        Socket sc = new Socket(host, subscriptionPort);
        InputStream in = sc.getInputStream();

        CharBuffer buffer = CharBuffer.allocate(50);
        char ch = 0;
        while (ch != EOL) {
            buffer.put(ch);
            ch = (char) in.read();
        }
        buffer.flip();
        String s = new String(buffer.array());
        int feedSubscriptionPort = Integer.parseInt(s.trim());
        if (LOGGER.isLoggable(Level.INFO)) {
            LOGGER.info("Response from Super Feed Manager Report Service " + port + " will connect at " + host + " "
                    + port);
        }

        // register the feed subscription queue with FeedLifecycleListener
        FeedLifecycleListener.INSTANCE.registerFeedReportQueue(feedId, outbox);
        RemoteSocketMessageListener listener = new RemoteSocketMessageListener(host, feedSubscriptionPort, outbox);
        listener.start();
    }
}

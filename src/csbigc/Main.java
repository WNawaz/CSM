/*
 * Main Entry Point
 */
package csbigc;

import etm.core.configuration.BasicEtmConfigurator;
import etm.core.configuration.EtmManager;
import etm.core.monitor.EtmMonitor;
import etm.core.monitor.EtmPoint;
import etm.core.renderer.SimpleTextRenderer;
import java.io.IOException;
import java.util.Random;

/**
 *
 * @author Waqas Nawaz Khokhar (wicky786@[khu.ac.kr, gmail.com, oslab.khu.ac.kr]), Phd Sage, UCLab, Computer Engineering Depratement,Kyung Hee University Korea
 */
public class Main {

    /**
     * @param args the command line arguments
     */
    private static EtmMonitor monitor;

    public static void main(String[] args) throws IOException {
        if (args.length == 0) {
            System.out.println("Invalid command line arguments...Just specify the configuration file path");
        } else {
            // configure measurement framework
            setup();
            //        String nodesFile = "dataset/coauthor/" + "nodes.txt", edgesFile = "dataset/coauthor/" + "edges.txt";
            //        int nodes = 5000, attr = 2;
            //        String nodesFile = "dataset/synth/" + "nodes.txt", edgesFile = "dataset/synth/" + "edges.txt";
            //        int nodes = 6, attr = 2;
            //        String nodesFile = "dataset/pblog/" + "nodes.txt", edgesFile = "dataset/pblog/" + "edges.txt";
            //        int nodes = 1490, attr = 1;
            //        String nodesFile = "dataset/email/" + "nodes.txt", edgesFile = "dataset/email/" + "edges.txt";
            //        int nodes = 4256, attr = 6;

//                    EtmPoint point = EtmManager.getEtmMonitor().createPoint("Algorithm");
            //        point.collect();
            CSBIGC obj = new CSBIGC(args[0]);
            obj.setDebug(true);
            obj.FindClusters();
//            point.collect();
//            CSBIGC.etmMonitor.render(new SimpleTextRenderer());
//            obj.WriteResults(appendToFile);

            //visualize results
//                    CNS.etmMonitor.render(new SimpleTextRenderer());
            // shutdown measurement framework
            tearDown();
        }

    }

    private static void setup() {
        BasicEtmConfigurator.configure();
        monitor = EtmManager.getEtmMonitor();
        monitor.start();
    }

    private static void tearDown() {
        monitor.stop();
    }
}

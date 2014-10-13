package csbigc;

/*
 * Based on the following paper Collaborative Similarity based Intra Graph
 * Clustering (Proposed iDeA)
 */
/**
 *
 * @author Waqas Nawaz Khokhar (wicky786@[khu.ac.kr, gmail.com,
 * oslab.khu.ac.kr]), Phd Sage, UCLab, Computer Engineering Depratement,Kyung
 * Hee University Korea
 */
import etm.core.configuration.EtmManager;
import etm.core.monitor.EtmMonitor;
import etm.core.monitor.EtmPoint;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Random;
import org.jgrapht.util.FibonacciHeap;
import org.jgrapht.util.FibonacciHeapNode;

/**
 *
 * @author Waqas Nawaz Khokhar (wicky786@[khu.ac.kr, gmail.com,
 * oslab.khu.ac.kr]), Phd Sage, UCLab, Computer Engineering Depratement,Kyung
 * Hee University Korea
 */
public class CSBIGC {
    /*
     * Breif Description about data members nodeCount(Number of Nodes),
     * edgeCount(Number of Edges), MaxDeg(maximum degree), simRange(Clustering
     * Similarity Range), weightList(Adjacency List for edge weights)
     * simList(Similarity List), degList (degree list), adjList(Adjacency List
     * for Node ID's), sumEW(sum of edge weights from a node) cluster(clustering
     * labels of the nodes), rankID(node index sorted by visit frequency
     * descending), rank(visited frequencies)
     */

    private int nodeCount, edgeCount, MaxDeg, attribs, attribsCount[], attribValCount, clusterCount;
    private float weightList[][], simList[], sumEW[], n2nSim[][];
    private float densityList[], entropyList[], attribW[];
    private int adjList[][], cluster[], bestCluster[], clusterVCount[], degList[];
    private boolean attribList[][], simCalcStatus[][];
    private String gNodeFName, gEdgeFName, configFName;
    private int ClusterID, startIndex;
    private float simThreshold, alpha, Entropy, FScore, Density, ObjFuncVal;
    private final float INF = 999999999.0f;
    private String delimeter;
    private static int iteration = 1;
    private boolean debug = false, isRandom;
    private ArrayList<Integer> centroids;
    public static final EtmMonitor etmMonitor = EtmManager.getEtmMonitor();

    /*
     * Multi-Argument Constructor
     */
    public CSBIGC(String configFile) throws IOException {
        startIndex = 1;
        delimeter = "\t";

        centroids = new ArrayList<Integer>();
        configFName = configFile;
        ReadConfigFile();
        System.out.print("\nGraph Info: \n\tTotal Nodes= " + nodeCount + " \n\tAttributes = " + attribs + " \n\tFiles = " + gNodeFName + "," + gEdgeFName);
        System.out.print("\n\tNumber of Clusters: " + clusterCount + " \n\tAlpha = " + alpha + "\n");
        System.out.print("Finding Maximum Degree... ");
        MaxDeg = FindMaxDegree(gEdgeFName);
        System.out.print(MaxDeg + " ... Done\n");

        System.out.print("Initializing...");
        Initialization();
        System.out.print("Done\n");
        System.out.print("Reading Graph Nodes...");
        ReadGraphNodes();
        System.out.print("Done\n");
        System.out.print("Reading Graph Edges...");
        ReadGraphEdges();
        System.out.print("Done\n");

        System.out.print("Node 2 Node Similarity Calculation...processing...");
        Node2NodeSimilarity();
        System.out.print("done\n");
    }

    private void ReadConfigFile() throws FileNotFoundException, IOException {
        //EtmPoint point = etmMonitor.createPoint("SA:ReadConfigFile");
        /*
         * Reading parameters
         */
//        try {
        FileInputStream fstream = new FileInputStream(configFName);
        // Get the object of DataInputStream
        DataInputStream in = new DataInputStream(fstream);
        BufferedReader br = new BufferedReader(new InputStreamReader(in));
        String tokens[];
        //Read File Line By Line
        nodeCount = Integer.parseInt(br.readLine());
        tokens = br.readLine().split(delimeter);
        attribs = Integer.parseInt(tokens[0]);
        attribsCount = new int[attribs];
        for (int i = 0; i < attribs; i++) {
            attribsCount[i] = Integer.parseInt(tokens[i + 1]);
            attribValCount += attribsCount[i];
        }
        gNodeFName = br.readLine(); // node file path
        gEdgeFName = br.readLine(); // edge file path
        clusterCount = Integer.parseInt(br.readLine());
        alpha = Float.parseFloat(br.readLine());
        isRandom = Boolean.parseBoolean(br.readLine());
        br.close();
        fstream.close();
//        } catch (Exception e) {
//            System.out.println("Invalid configuration file (problem with file reading)");
//        }
        //point.collect();
    }

    private int FindMaxDegree(String fileName) throws IOException {
        int max_degree = 0;
        boolean adj[][] = new boolean[nodeCount][nodeCount];
        int nodeDegList[] = new int[nodeCount];
        for (int i = 0; i < nodeCount; i++) {
            nodeDegList[i] = 0;
            for (int j = 0; j < nodeCount; j++) {
                adj[i][j] = false;
            }
        }

        FileInputStream fstream = new FileInputStream(fileName);
        // Get the object of DataInputStream
        DataInputStream in = new DataInputStream(fstream);
        BufferedReader br = new BufferedReader(new InputStreamReader(in));
        String strLine;
        br.readLine();
        //Read File Line By Line
        while ((strLine = br.readLine()) != null) {
            String tokens[] = strLine.split(delimeter);
            int node1ID = Integer.parseInt(tokens[0]) - startIndex;
            int node2ID = Integer.parseInt(tokens[1]) - startIndex;
            if (node1ID != node2ID && node1ID < (nodeCount) && node2ID < (nodeCount)) {
                adj[node1ID][node2ID] = true;
                adj[node2ID][node1ID] = true;
                //nodeDegList[node1ID] = nodeDegList[node1ID] + 1;
                //nodeDegList[node2ID] = nodeDegList[node2ID] + 1;
            }
        }
        for (int i = 0; i < nodeCount; i++) {
            for (int k = 0; k < nodeCount; k++) {
                if (adj[i][k]) {
                    nodeDegList[i]++;
                }
            }
        }
        for (int j = 0; j < nodeCount; j++) {
            if (nodeDegList[j] > max_degree) {
                max_degree = nodeDegList[j];
            }
        }
        return max_degree;
    }

    private void Initialization() {
        adjList = new int[nodeCount][MaxDeg];
        simCalcStatus = new boolean[nodeCount][MaxDeg];
        n2nSim = new float[nodeCount][nodeCount];
        attribList = new boolean[nodeCount][attribValCount];
        attribW = new float[attribs];
        weightList = new float[nodeCount][MaxDeg];
        simList = new float[nodeCount];
        degList = new int[nodeCount];
        sumEW = new float[nodeCount];
        cluster = new int[nodeCount];
        bestCluster = new int[nodeCount];
        edgeCount = 0;
        Entropy = ObjFuncVal = 0.0f;
        Density = FScore = 0.0f;

        for (int i = 0; i < nodeCount; i++) {
            for (int j = 0; j < MaxDeg; j++) {
                adjList[i][j] = -1;
                weightList[i][j] = -1.0f;
                simCalcStatus[i][j] = false;
            }
            for (int k = 0; k < attribValCount; k++) {
                attribList[i][k] = false;
            }
            for (int l = 0; l < nodeCount; l++) {
                n2nSim[i][l] = -1.0f;
            }
            degList[i] = 0;
            simList[i] = 0;
            sumEW[i] = -1.0f;
            cluster[i] = -1;
            bestCluster[i] = -1;
        }
        for (int k = 0; k < attribs; k++) {
            attribW[k] = 1;
        }
    }

    public void setDebug(boolean status) {
        this.debug = status;
    }

    public void Re_Init() {
        simList = new float[nodeCount];
        cluster = new int[nodeCount];
        bestCluster = new int[nodeCount];
        Entropy = ObjFuncVal = 0.0f;
        Density = FScore = 0.0f;
        for (int i = 0; i < nodeCount; i++) {
            simList[i] = -1;
            cluster[i] = -1;
            bestCluster[i] = -1;
        }
        //iteration = 1;
    }

    private void GenerateSyntheticGraph() {
        Random rand = new Random();
        for (int i = 0; i < nodeCount; i++) {
            int count = 1 + (int) (rand.nextDouble() * attribValCount);
            for (int a = 0; a < count; a++) {
                int attribID = (int) (rand.nextDouble() * attribValCount);
                attribList[i][attribID] = true;
            }
            count = (int) (rand.nextDouble() * MaxDeg);
            for (int j = 0; j < count; j++) {
                int node = (int) (rand.nextDouble() * nodeCount);
                float weight = (float) rand.nextDouble();
                edgeCount++;
                for (int ka = 0; ka < MaxDeg; ka++) {
                    if (adjList[i][ka] == -1) {
                        adjList[i][ka] = node;
                        weightList[i][ka] = weight;
                        break;
                    }
                }
                for (int kb = 0; kb < MaxDeg; kb++) {
                    if (adjList[node][kb] == -1) {
                        adjList[node][kb] = i;
                        weightList[node][kb] = weight;
                        break;
                    }
                }
            }
        }

    }

    private void ReadGraphNodes() throws FileNotFoundException, IOException {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:ReadGraphData");
        /*
         * Reading Graph nodes with attributes
         */
        FileInputStream fstream = new FileInputStream(gNodeFName);
        // Get the object of DataInputStream
        DataInputStream in = new DataInputStream(fstream);
        BufferedReader br = new BufferedReader(new InputStreamReader(in));
        String strLine, tokens[];
        int padding = 0;
        //Read File Line By Line
        //br.readLine();
        while ((strLine = br.readLine()) != null) {
            //System.out.println(strLine);
            tokens = strLine.split(delimeter);
            int nodeID = Integer.parseInt(tokens[0]) - startIndex;
            if (nodeID < (nodeCount)) {
                for (int i = 1; i <= attribs; i++) {
                    attribList[nodeID][padding + Integer.parseInt(tokens[i]) - startIndex] = true;
                    padding += attribsCount[i - 1];
                }//end for
            }//end if
            padding = 0;
        }//end while
        br.close();
        fstream.close();
        //point.collect();
    }

    private void ReadGraphEdges() throws FileNotFoundException, IOException {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:ReadGraphData");
        FileInputStream fstream = new FileInputStream(gEdgeFName);
        // Get the object of DataInputStream
        DataInputStream in = new DataInputStream(fstream);
        BufferedReader br = new BufferedReader(new InputStreamReader(in));
        String strLine;
        //Read File Line By Line
        //br.readLine();
        while ((strLine = br.readLine()) != null) {
            String tokens[] = strLine.split(delimeter);
            int node1ID = Integer.parseInt(tokens[0]) - startIndex;
            int node2ID = Integer.parseInt(tokens[1]) - startIndex;
            float weight = Float.parseFloat(tokens[2]);
            if (node1ID != node2ID && (node1ID < node2ID) && node1ID < (nodeCount) && node2ID < (nodeCount)) {
                edgeCount++;
                for (int j = 0; j < MaxDeg; j++) {
                    if (adjList[node1ID][j] == node2ID) {
                        break;
                    }
                    if (adjList[node1ID][j] == -1) {
                        adjList[node1ID][j] = node2ID;
                        weightList[node1ID][j] = weight;
                        break;
                    }
                }
                for (int j = 0; j < MaxDeg; j++) {
                    if (adjList[node2ID][j] == node1ID) {
                        break;
                    }
                    if (adjList[node2ID][j] == -1) {
                        adjList[node2ID][j] = node1ID;
                        weightList[node2ID][j] = weight;
                        break;
                    }
                }
            }
        }
        br.close();
        fstream.close();
        //set up degree list, find max degree, sum weights and max weight
        for (int n = 0; n < nodeCount; n++) {
            degList[n] = DegreeOfNode(n);
            sumEW[n] = SumOfWeights(n);
        }
        //point.collect();

    }

    private float SumOfWeights(int nodeIndex) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:SumOfWeights");
        float weightedSum = 0f;
        for (int i = 0; i < MaxDeg; i++) {
            if (adjList[nodeIndex][i] != -1) {
                weightedSum += weightList[nodeIndex][i];
            } else {
                break;
            }
        }
        //point.collect();
        return (weightedSum);
    }

    private int DegreeOfNode(int nodeIndex) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:DegreeOfNode");
        int degree = 0;
        for (int i = 0; i < MaxDeg; i++) {
            if (adjList[nodeIndex][i] != -1) {
                degree++;
            } else {
                break;
            }
        }
        //point.collect();
        return (degree);
    }

    private void FindClusters(float alphaVal, float thetaVal) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:FindClusters");
        //Clustering process started
        System.out.print("Clustering...Alpha( " + alphaVal + " )...Sim-Threshold( " + thetaVal + " )...");
        simThreshold = thetaVal;
        alpha = alphaVal;
        ClusterID = 0;
        int selectedNode = 0, adjNode = 0;
        boolean terminate = false;
        while (!terminate) {
            //re-initialize all similarity values
            for (int i = 0; i < nodeCount; i++) {
                simList[i] = -1;
            }
            //calculate basic similarities from the selected node to every other adjacent node
            for (int j = 0; j < MaxDeg; j++) {
                adjNode = adjList[selectedNode][j];
                if (adjNode != -1) {
                    simList[adjNode] = (alpha * DirectStrctSim(selectedNode, adjNode)) + ((1 - alpha) * DirectContextSim(selectedNode, adjNode));
                } else {
                    break;
                }
            }

            //calculate extended similarities from the selected node to all other reachable nodes
            NodeSimilarity(selectedNode);
            //NodeSimilarityUsingHeap(selectedNode);

            //calculate the similarities from the selected node to all isolated nodes
            IsolatedNodeSimilarity(selectedNode);

            //update the belongings of current cluster items
            cluster[selectedNode] = ClusterID;
            for (int n = 0; n < nodeCount; n++) {
                if (simList[n] >= simThreshold && cluster[n] == -1) {
                    cluster[n] = ClusterID;
//                    System.out.println("NodeID = " + n +" in Cluster = " + ClusterID);
                }
            }

            //prepare next starting node for the next cluster
            boolean isComplete = true;
            for (int n = 0; n < nodeCount; n++) {
                if (cluster[n] == -1) {
                    selectedNode = n;
                    ClusterID++;
                    isComplete = false;
                    break;
                }
            }
            if (isComplete) {
                terminate = true;
            }
        }
        System.out.print(" Clusters Found = " + (ClusterID + 1) + " ...");
        System.out.print("Done\n");
        //Clustering process completed here

        //point.collect();
    }//Find Natural Clusters based upon Threshold

    private void pickCentroids() {
        int i, j, k, pos;
        boolean unused[] = new boolean[nodeCount];
        for (int s = 0; s < nodeCount; s++) {
            unused[s] = true;
        }
        //pick top degree N nodes as initial centroids
        for (i = 0; i < clusterCount; i++) {
            pos = -1;
            for (j = 0; j < nodeCount; j++) {
                if (pos == -1) {
                    for (k = 0; k < nodeCount; k++) {
                        if (unused[k]) {
                            pos = k;
                            break;
                        }
                    }
                }
                if (unused[j] && (degList[j] > degList[pos])) {
                    pos = j;
                }
            }
            centroids.add(pos);
            unused[pos] = false;
        }
    }

    public boolean FindClusters() throws FileNotFoundException, IOException {
        EtmPoint point = etmMonitor.createPoint("CS:FindClusters");

        if (clusterCount > nodeCount) {
            System.err.println("No of clusters exceeded the number of objects to be clustered.");
            return false;
        }
        int maxIter = 10;
        System.out.println("Clustering...Started\n\tAlpha: " + alpha + "\n\tNo. of Clusters: " + clusterCount);
        //Delaration and initialization of variables

        Random rand = new Random();
        int centroidList[] = new int[clusterCount];
        int clusterItemsList[][] = new int[clusterCount][nodeCount];
        float clusterSimList[][] = new float[clusterCount][nodeCount];
        for (int c = 0; c < clusterCount; c++) {
            centroidList[c] = -1;
            for (int n = 0; n < nodeCount; n++) {
                clusterItemsList[c][n] = -1;
                clusterSimList[c][n] = 0.0f;
            }
        }

        if (debug) {
            System.out.print("Initial Centroids Selection...processing...");
        }
        /**
         * ********************************************************************************************************************************************
         */
        /*
         * Centroid Selection Stage (once at start)
         */
        //**********************************************************************
        //seeds as a centroid of each cluster
        if (!isRandom) {
            pickCentroids();
            for (int i = 0; i < clusterCount; i++) {
                int index = centroids.get(i);
                cluster[index] = i;
                centroidList[i] = index;
                clusterItemsList[i][0] = index;
            }
        } else {
            //**********************************************************************
            //Randomly select clusterCount seeds as a centroid of each cluster
            for (int i = 0; i < clusterCount;) {
                int index = (int) (rand.nextDouble() * nodeCount);
                boolean exist = false;
                for (int j = 0; j < clusterCount; j++) {
                    if (centroidList[j] == index) {
                        exist = true;
                    }
                }
                if (!exist) {
                    cluster[index] = i;
                    centroidList[i] = index;
                    clusterItemsList[i][0] = index;
                    i++;
                }
            }
        }
        //**********************************************************************
        if (debug) {
            System.out.print("done\n");
        }
        float bestDensity = -1.0f, bestEntropy = 99.0f, bestFscore = -1.0f, bestObjFuncValue = -99.0f;
        /**
         * ********************************************************************************************************************************************
         */
        for (int iter = 1; iter <= maxIter; iter++) {
            /*
             * Evoluation Stage
             */
            if (debug) {
                System.out.print("Iteration: " + iter + "\n");
            }
            /*
             * Re-Union
             */

            if (debug) {
                System.out.print("\tCluster formation...processing...");
            }
            int bestCentroid;
            boolean isCentroid = false;
            for (int n = 0; n < nodeCount; n++) {
                //make sure the selected node 'n' is not centroid
                for (int i = 0; i < clusterCount; i++) {
                    if (centroidList[i] == n) {
                        isCentroid = true;
                        break;
                    }
                }
                if (!isCentroid) {
                    //determine which nearest cluster centroid
                    bestCentroid = 0;
                    for (int c = 1; c < clusterCount; c++) {
                        if (n2nSim[n][centroidList[bestCentroid]] > n2nSim[n][centroidList[c]]) {
                            bestCentroid = c;
                        }
                    }
                    cluster[n] = bestCentroid;
                    //add this item to appropriate cluster items list
                    for (int j = 0; j < nodeCount; j++) {
                        if (clusterItemsList[bestCentroid][j] == -1) {
                            clusterItemsList[bestCentroid][j] = n;
                            break;
                        }
                    }
                }
                isCentroid = false;
            }
            if (debug) {
                System.out.print("done\n");
            }
            /**
             * ********************************************************************************************************************************************
             */
            /*
             * Evaluate the Optimization Function (If the Clusters are stable,
             * no interchange of nodes/items occures)
             */
            if (debug) {
                System.out.print("\tEvaluation...processing...");
            }
            DensityCheck();
            EntropyCheck();
            FScoreCheck();
            if (alpha == 1.0f) {
                ObjFuncVal = (alpha * Density);
            } else if (alpha == 0.0f) {
                ObjFuncVal = 1/((1 - alpha) * Entropy);
            } else {
                ObjFuncVal = (alpha * Density) / ((1 - alpha) * Entropy);
            }
            //ObjFuncVal = Density + (1 / Entropy);
            //WriteObjFunc(iter,true);
            if (ObjFuncVal > bestObjFuncValue /*
                     * Density > bestDensity && Entropy < bestEntropy
                     */) {
                bestObjFuncValue = ObjFuncVal;
                bestDensity = Density;
                bestEntropy = Entropy;
                bestFscore = FScore;
                if (debug) {
                    System.out.print("Best objFuncValue( " + bestObjFuncValue + " )...");
                    System.out.print("Best Density( " + bestDensity + " )...");
                    System.out.print("Best Entropy( " + bestEntropy + " )...");
                    System.out.print("Best FScore( " + bestFscore + " )...");
                }
                System.arraycopy(cluster, 0, bestCluster, 0, nodeCount);
            } else {
                break;
            }
            if (debug) {
                System.out.print("objFuncValue( " + ObjFuncVal + " )...");
                System.out.print("Entropy( " + Entropy + " )...");
                System.out.print("Density( " + Density + " )...");
                System.out.print("FScore( " + FScore + " )...done\n");
            }
            iteration = iter;
            WriteResults(true);
            /**
             * ********************************************************************************************************************************************
             */
            /*
             * Choose Appropriate Centroid for each cluster
             */
            if ((iter + 1) <= maxIter) {

                if (debug) {
                    System.out.print("\tCentroid Re-Selection...processing...");
                }
                float maxSimSum, simSum;
                for (int c = 0; c < clusterCount; c++) {
                    maxSimSum = INF;//-1;
                    for (int n = 0; n < nodeCount; n++) {
                        simSum = 0.0f;
                        //check/measure the closeness of this node (n) to all others (m) in this cluster (c)
                        if (clusterItemsList[c][n] == -1) {
                            break;
                        }
                        for (int m = 0; m < nodeCount; m++) {
                            if (clusterItemsList[c][m] == -1) {
                                break;
                            } else if (n != m) {
                                int node1 = clusterItemsList[c][n], node2 = clusterItemsList[c][m];
                                simSum += n2nSim[node1][node2];
                            }
                        }
                        //determine which is the best candidate for being a centroid
                        if (simSum < maxSimSum) {
                            maxSimSum = simSum;
                            centroidList[c] = clusterItemsList[c][n];
                            cluster[clusterItemsList[c][n]] = c;
                        }
                    }
                }
                if (debug) {
                    System.out.print("done\n");
                    /*
                     * Re-Initialization stage (pre-paring for the next
                     * iteration)
                     */
                    System.out.print("\tPreparing for next iteration...processing...");
                }
                for (int i = 0; i < nodeCount; i++) {
                    simList[i] = -1;
                }
                for (int c = 0; c < clusterCount; c++) {
                    for (int n = 0; n < nodeCount; n++) {
                        clusterItemsList[c][n] = -1;
                        clusterSimList[c][n] = 0.0f;
                    }
                }
                if (debug) {
                    System.out.print("done\n");
                }
            }
            /**
             * ********************************************************************************************************************************************
             */
        }
        System.out.print("Clustering...finished.\n");
        Density = bestDensity;
        Entropy = bestEntropy;
        FScore = bestFscore;
        if (debug) {
            System.out.println("Best Desnity: " + Density);
            System.out.println("Best Entropy: " + Entropy);
            System.out.println("Best FScore: " + FScore);
            System.out.println("******************************************************************************************\n");
        }
        //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
        point.collect();
        return true;
    }// Search Specified No. of Cluster

    private void Node2NodeSimilarity() {
        EtmPoint point = etmMonitor.createPoint("CS:Node2NodeSimilarity");
        for (int n = 0; n < nodeCount; n++) {
            simList[n] = -1;
        }
        int adjNode = 0;
        for (int i = 0; i < nodeCount; i++) {
            //calculate basic similarities from the selected node to every other adjacent node
            for (int a = 0; a < MaxDeg; a++) {
                adjNode = adjList[i][a];
                if (adjNode != -1) {
                    if (n2nSim[i][adjNode] == -1) {
                        n2nSim[i][adjNode] = 1 / ((alpha * DirectStrctSim(i, adjNode)) + ((1 - alpha) * DirectContextSim(i, adjNode)));
                        n2nSim[adjNode][i] = n2nSim[i][adjNode];
                    }
                } else {
                    break;
                }

            }
        }
        for (int j = 0; j < nodeCount; j++) {
            //calculate extended similarities from the selected node to all other non adjacent but reachable nodes
            //NodeSimilarity(j);
            NodeSimilarityUsingHeap(j);
            //calculate the similarities from the selected node to all isolated nodes
            IsolatedNodeSimilarity(j);

            //assigning and re-initialize all similarity values
            for (int k = 0; k < nodeCount; k++) {
                if (simList[k] != -1) {
                    n2nSim[j][k] = simList[k];
                    n2nSim[k][j] = n2nSim[j][k];
                    simList[k] = -1;
                }
            }
        }
        point.collect();
    }

    private void IsolatedNodeSimilarity(int sourceNode) {
        for (int i = 0; i < nodeCount; i++) {
            if (n2nSim[sourceNode][i] == -1) {
                n2nSim[sourceNode][i] = ((1 - alpha) * DirectContextSim(sourceNode, i));
            }
        }
    }

    private void NodeSimilarityUsingHeap(int startNode) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:IndirectNodeSimilarityUsingHeap");
        //This uses a fast 1 to ALL SP algorithm based in a Dijkstra-like implementation
        //using a window-queue with minimum variable size (studied and developed in 2010 by E.Tiakas)
        //for an un-directed graph

        int parent[] = new int[nodeCount];
        float dist[] = new float[nodeCount];
        boolean inque[] = new boolean[nodeCount];
        int i, v, u;
        float p, weight;

        for (i = 0; i < nodeCount; i++) {
            parent[i] = -1;
            dist[i] = INF;
            inque[i] = false;
        }
        v = startNode;
        dist[v] = 0;
        simList[v] = 1;
        p = 1.0f;

        FibonacciHeap H = new FibonacciHeap();
        H.insert(new FibonacciHeapNode(v), 0f);
        while (H.size() > 0) {
            v = (Integer) H.removeMin().getData();
            for (i = 0; i < MaxDeg; i++) {
                u = adjList[v][i];
                if (u != -1) {
                    weight = weightList[v][i];
                    if (dist[u] > dist[v] + weight) {
                        dist[u] = dist[v] + weight;
                        parent[u] = v;
                        simList[u] = simList[v] * n2nSim[v][u];//((alpha * DirectStrctSim(v, u)) + ((1 - alpha) * DirectContextSim(v, u)));
//                        if (inque[u])
//                        {
//                            try
//                            {
//                                //H.decreaseKey(new FibonacciHeapNode(u), dist[u]);
//                            }
//                            catch(Exception e)
//                            {
//                                //System.out.println("\n"+e.getMessage().toString());
//                            }
//                        }
                    }
                    if (!inque[u] && cluster[u] == -1) {
                        H.insert(new FibonacciHeapNode(u), dist[u]);
                        inque[u] = true;
                    }
                } else {
                    break;
                }
            }//for(i=0;i<MaxDeg;i++)
        }//while(H.size() > 0)
        //point.collect();

    }//Indirect Node Similarity

    private float DistBtwNodesUsingHeap(int sourceNode, int destNode) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:IndirectNodeSimilarityUsingHeap");
        //This uses a fast 1 to ALL SP algorithm based in a Dijkstra-like implementation
        //using a window-queue with minimum variable size (studied and developed in 2010 by E.Tiakas)
        //for an un-directed graph
        simList[destNode] = 0.0f;
        /**
         * *******************************************************************
         */
        /*
         * sourceNode and destNode are directly connected with each other
         */
        /**
         * *******************************************************************
         */
        for (int k = 0; k < MaxDeg; k++) {
            int adjNode = adjList[sourceNode][k];
            if (adjNode == destNode) {
                simList[destNode] = (alpha * DirectStrctSim(sourceNode, destNode)) + ((1 - alpha) * DirectContextSim(sourceNode, destNode));
                return simList[destNode];
            } else if (adjNode == -1) {
                break;
            }
        }
        /**
         * *******************************************************************
         */
        /*
         * when sourceNode and destNode are in-directly connected
         */
        /**
         * *******************************************************************
         */
        int parent[] = new int[nodeCount];
        float dist[] = new float[nodeCount];
        boolean inque[] = new boolean[nodeCount];
        int i, v, u;
        float p, weight;

        for (i = 0; i < nodeCount; i++) {
            parent[i] = -1;
            dist[i] = INF;
            inque[i] = false;
        }
        v = sourceNode;
        dist[v] = 0;
        simList[v] = 1;
        p = 1.0f;

        FibonacciHeap H = new FibonacciHeap();
        H.insert(new FibonacciHeapNode(v), 0f);
        while (H.size() > 0) {
            v = (Integer) H.removeMin().getData();
            for (i = 0; i < MaxDeg; i++) {
                u = adjList[v][i];
                if (u != -1) {
                    weight = weightList[v][i];
                    if (dist[u] > dist[v] + weight) {
                        dist[u] = dist[v] + weight;
                        parent[u] = v;
                        simList[u] = simList[v] * ((alpha * DirectStrctSim(v, u)) + ((1 - alpha) * DirectContextSim(v, u)));
                        if (u == destNode) {
                            return simList[u];
                        }
                    }
                    if (!inque[u] && cluster[u] == -1) {
                        H.insert(new FibonacciHeapNode(u), dist[u]);
                        inque[u] = true;
                    }
                } else {
                    break;
                }
            }//for(i=0;i<MaxDeg;i++)
        }//while(H.size() > 0)
        /**
         * *******************************************************************
         */
        /*
         * when sourceNode and destNode are isolated
         */
        /**
         * *******************************************************************
         */
        simList[destNode] = (1 - alpha) * DirectContextSim(sourceNode, destNode);
        return simList[destNode];

        //point.collect();
    } //Indirect Similarity between nodes

    private void NodeSimilarity(int startNode) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:IndirectNodeSimilarity");
        //This uses a fast 1 to ALL SP algorithm based in a Dijkstra-like implementation
        //using a window-queue with minimum variable size (studied and developed in 2010 by E.Tiakas)
        //for an un-directed graph
        int parent[] = new int[nodeCount];
        float dist[] = new float[nodeCount];
        int inque[] = new int[nodeCount];
        int q[] = new int[nodeCount * MaxDeg];
        float qw[] = new float[nodeCount * MaxDeg];
        int i, v, u;
        int qe, qs, qv, temp;
        float p, mind, weight, tempw;

        for (i = 0; i < nodeCount; i++) {
            parent[i] = -1;
            dist[i] = INF;
            inque[i] = 0;
        }
        for (i = 0; i < MaxDeg * nodeCount; i++) {
            q[i] = -1;
            qw[i] = INF;
        }
        qs = 0;
        qe = 0;
        v = startNode;
        dist[v] = 0;
        simList[v] = 1;
        p = 1.0f;

        while (qe >= qs) {
            for (i = 0; i < MaxDeg; i++) {
                u = adjList[v][i];
                if (u != -1) {
                    weight = weightList[v][i];
                    if (dist[u] > dist[v] + weight) {
                        dist[u] = dist[v] + weight;
                        parent[u] = v;
                        simList[u] = simList[v] * ((alpha * DirectStrctSim(v, u)) + ((1 - alpha) * DirectContextSim(v, u)));
                    }
                    if (inque[u] == 0 && cluster[u] == -1) //visit[u] == 0 && Cluster[u] == -1)
                    {
                        q[qe] = u;
                        qw[qe] = dist[u];
                        qe = qe + 1;
                        inque[u] = 1;
                    }
                } else {
                    break;
                }
            }
            mind = INF;
            qv = qs;
            for (i = qs; i < qe; i++) {
                if (dist[q[i]] < mind) {
                    mind = dist[q[i]];
                    v = q[i];
                    qv = i;
                }
            }
            temp = q[qv];
            q[qv] = q[qs];
            q[qs] = temp;
            tempw = qw[qv];
            qw[qv] = qw[qs];
            qw[qs] = tempw;
            qs = qs + 1;
        }

        //point.collect();
    }//Indirect Node Similarity

    private float DirectContextSim(int i, int j) {
        float simValue = 0.0f, weight = 1.0f;
        int common = 0, union = 0;
        for (int a = 0; a < attribValCount; a++) {
            if (attribList[i][a] && attribList[j][a]) {
                //*****************************************//
                int temp = 0;
                for (int b = 0; b < attribs; b++) {
                    if (a < (temp + attribsCount[b])) {
                        weight *= attribW[b];
                        break;
                    } else {
                        temp += attribsCount[b];
                    }
                }
                //*****************************************//
                common++;
                union++;
            } else if (attribList[i][a] || attribList[j][a]) {
                union++;
            }
        }
        simValue = (float) (common * weight) / union;
        return simValue;
    } //Direct Contextual Similarity

    private float DirectStrctSim(int a, int b) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:DirectNodeSimilarity");
        //calculate the ratio of common and total neigbhors
        float simValue = 0.0f;
        float wSum = 0.0f, wAB = 0.0f;
        int index = 0;
        //for all edges of a
        for (index = 0; index < MaxDeg; index++) {
            if (adjList[a][index] == -1) {
                break;
            }
            if (adjList[a][index] == b) {
                wAB = weightList[a][index];
            }
            wSum += weightList[a][index];
        }
        //for all edges of b
        for (index = 0; index < MaxDeg; index++) {
            if (adjList[b][index] == -1) {
                break;
            }
            wSum += weightList[b][index];
        }
        simValue = wAB / (wSum - wAB);
        //System.out.println((a+1) + "," + (b+1) + "," + simValue);
        //point.collect();
        return (simValue);
    } //Direct Structural Similarity

    private float DirectStrctSim_old(int a, int b) {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:DirectNodeSimilarity");
        //calculate the ratio of common and total neigbhors
        float simValue = 0;
        int common = 0;
        for (int adjA = 0; adjA < MaxDeg; adjA++) {
            if (adjList[a][adjA] == -1) {
                break;
            }
            for (int adjB = 0; adjB < MaxDeg; adjB++) {
                if (adjList[b][adjB] == -1) {
                    break;
                } else if (adjList[a][adjA] == adjList[b][adjB]) {
                    common++;
                    break;
                }
            }
        }
        int denom = (degList[a] + degList[b]) - (common + 2);
        for (int adj = 0; adj < MaxDeg; adj++) {
            if (adjList[a][adj] == b) {
                simValue = ((float) common / denom) * weightList[a][adj];
            }
        }
        //point.collect();
        return (simValue);
    } //Direct Structural Similarity

    public float DensityCheck() {
        //initialize
        int adjListTemp[][] = new int[nodeCount][MaxDeg];
        for (int i = 0; i < nodeCount; i++) {
            System.arraycopy(adjList[i], 0, adjListTemp[i], 0, MaxDeg);
        }
        densityList = new float[clusterCount];
        for (int k = 0; k < clusterCount; k++) {
            densityList[k] = 0;
        }
        int clusterEdgeCount = 0;
        float density = 0;
        //
        for (int i = 0; i < clusterCount; i++) {
            for (int j = 0; j < nodeCount; j++) {
                if (cluster[j] == i) {
                    for (int k = 0; k < MaxDeg; k++) {
                        if (adjListTemp[j][k] == -1) {
                            break;
                        } else if (adjListTemp[j][k] == -2) {
                            continue;
                        } else if (cluster[adjListTemp[j][k]] == i) {
                            clusterEdgeCount++;
                            //do not consider single edge multiple times
                            for (int n = 0; n < MaxDeg; n++) {
                                if (adjListTemp[adjListTemp[j][k]][n] == -1) {
                                    break;
                                }
                                if (adjListTemp[adjListTemp[j][k]][n] == j) {
                                    adjListTemp[adjListTemp[j][k]][n] = -2;
                                }
                            }//end for
                        }//end if
                    }//end for
                }//end if
            }//end for
            densityList[i] = (float) clusterEdgeCount / edgeCount;
            density += densityList[i];
            clusterEdgeCount = 0;
        }
        Density = density;
        //System.out.println("Accumulative Density = " + density);
        return Density;
    }

    public float EntropyCheck() {
        float accumEntropy = 0, attribWSum = 0, percentV = 0;
        clusterVCount = new int[clusterCount];
        entropyList = new float[clusterCount];
        for (int i = 0; i < clusterCount; i++) {
            entropyList[i] = 0;
            clusterVCount[i] = 0;
        }
        for (int j = 0; j < attribs; j++) {
            attribWSum += attribW[j];
        }
        for (int k = 0; k < nodeCount; k++) {
            if (cluster[k] != -1) {
                clusterVCount[cluster[k]] += 1;
            }
        }

        int index = 0;
        for (int a = 0; a < attribs; a++) {
            percentV = 0;
            for (int c = 0; c < clusterCount; c++) {
                float avg = (float) clusterVCount[c] / nodeCount, entrop = 0.0f;
                int count = 0;
                for (int aVal = index; aVal < (index + attribsCount[a]); aVal++) {
                    count = 0;
                    for (int n = 0; n < nodeCount; n++) {
                        if (cluster[n] == c) {
                            if (attribList[n][aVal]) {
                                count++;
                            }
                        }
                    }
                    float p = (float) count / clusterVCount[c];
                    if (p != 0) {
//                        float denom = (float) (Math.log((index + attribsCount[a])) / Math.log(2));
//                        if(denom != 0)
//                        {
                        entrop += (-p * (float) (Math.log(p) / Math.log(2)));// / denom;
//                        }
                    }
                }
                percentV = percentV + (avg * entrop);
            }
            accumEntropy += (float) (attribW[a] / attribWSum) * percentV;
            index += attribsCount[a];
        }
        Entropy = accumEntropy;
        //System.out.println("Accumulative Entropy = " + accumEntropy);
        return accumEntropy;
    }

    public float FScoreCheck() {
        //Declaration
        int attribVCountAll[] = new int[attribValCount];
        int attribVCountCluster[][] = new int[clusterCount][attribValCount];
        //Initialization
        for (int c = 0; c < clusterCount; c++) {
            for (int a = 0; a < attribValCount; a++) {
                attribVCountCluster[c][a] = 0;
            }
        }
        //Calculations
        for (int a = 0; a < attribValCount; a++) {
            attribVCountAll[a] = 0;
            for (int i = 0; i < nodeCount; i++) {
                if (attribList[i][a]) {
                    attribVCountAll[a] += 1;
                    attribVCountCluster[cluster[i]][a] += 1;
                }
            }
        }
        //FMeasure for each Cluster
        float P = 0f, R = 0f, M = 0f, Sum = 0f, fmeasure = -1.0f;
        int denom = 0;
        for (int a = 0; a < attribValCount; a++) {
            if (attribVCountAll[a] > 0) {
                for (int c = 0; c < clusterCount; c++) {
                    P = (float) attribVCountCluster[c][a] / clusterVCount[c];
                    R = (float) attribVCountCluster[c][a] / attribVCountAll[a];
                    M = (2 * P * R) / (P + R);
                    if (fmeasure < M) {
                        fmeasure = M;
                    }
                }
                Sum += fmeasure; //* ((float) attribVCountAll[a] / nodeCount);
                denom++;
                fmeasure = -1.0f;
            }
        }
        float overallFScore = (Sum / denom);
        FScore = overallFScore;
        return FScore;
    }

    public void WriteResults(boolean append) throws FileNotFoundException, IOException {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:WriteResults");

        //Write to file
        System.out.print("Writing to File...");
        FileOutputStream fostream = new FileOutputStream/*
                 * ("cluseters"+ alpha +".txt",append);//
                 */("clusters_" + nodeCount + "_" + clusterCount + "_" + alpha + ".txt", append);
        BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(fostream));
        bw.write("Iteration: " + iteration + ", \nNo. of Clusters: " + clusterCount + ", Density: " + Density + ", Entropy: " + Entropy + ", Fmeasure: " + FScore);
//*****************************************************************************//
        //Entropy, Density, Fmeasure
//        if (iteration == 1) {
//            bw.write("ITERATION" + delimeter + " ALPHA" + delimeter + "NO. OF NODES" + delimeter + "NO. OF ATTRIBUTES" + delimeter + "MAX DEGREE" + delimeter + "NO. OF CLUSTERS" + delimeter + "DENSITY" + delimeter + "ENTROPY" + delimeter + "FSCORE" + delimeter + "ObjFVal");
//            bw.newLine();
//        }
//        bw.write((iteration++) + delimeter + Float.toString(alpha) + delimeter + nodeCount + delimeter + attribs + delimeter + MaxDeg + delimeter + clusterCount + delimeter + Density + delimeter + Entropy + delimeter + FScore + delimeter + ((alpha * Density) - ((1 - alpha) * Entropy)));
//        bw.newLine();
//*****************************************************************************//
//        //read Users ID and Name mapping from file
//        String users[] = new String[nodeCount];
//        FileInputStream fistream = new FileInputStream("users.txt");
//        // Get the object of DataInputStream
//        DataInputStream in = new DataInputStream(fistream);
//        BufferedReader br = new BufferedReader(new InputStreamReader(in));
//        String strLine = null, tokens[];
//        //Read File Line By Line
//        br.readLine();
//        br.readLine(); //skip un-necessary lines
//        while ((strLine = br.readLine()) != null) {
//            tokens = strLine.split(delimeter);
//            //user ID, Name, Designation
//            if (tokens.length == 3) {
//                users[Integer.parseInt(tokens[0]) - 1] = tokens[1] + "(" + tokens[2] + ")";
//            } else {
//                users[Integer.parseInt(tokens[0]) - 1] = tokens[1];
//            }
//        }
//        br.close();
//        in.close();
//        fistream.close();

        bw.write("\nUID\tClusterID");
        bw.newLine();
        //writing users ID and corresponding cluster ID
        for (int c = 0; c < clusterCount; c++) {
//            int counter = 0;
            //bw.write("Cluster: " + (c + 1));
            //bw.newLine();
            //bw.write("-----------");
            //bw.newLine();
            for (int n = 0; n < nodeCount; n++) {
                if (bestCluster[n] == c) {
                    bw.write((n + 1) + "\tc" + (c + 1));
                    bw.newLine();
                }
            }
            //bw.newLine();
        }
        bw.close();
        fostream.close();
        System.out.print("Done (See the clusters.txt file).\n");
        //point.collect();
    }

    private void WriteObjFunc(int iteration, boolean append) throws FileNotFoundException, IOException {
        //EtmPoint point = etmMonitor.createPoint("TransNodeSim:WriteResults");
        if (debug) {
            System.out.print("Writing to File...");
        }
        String delim = "\t";
        FileOutputStream fstream = new FileOutputStream("Graph_Clusters_ObjFunc.txt", append);
        BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(fstream));
        if (iteration == 1) {
            bw.write("ITERATION" + delim + " ALPHA" + delim + "NO. OF CLUSTERS" + delim + "ObjFuncVal");
            bw.newLine();
        }
        bw.write((iteration) + delim + alpha + delim + clusterCount + delim + ObjFuncVal);
        bw.newLine();
        bw.close();
        fstream.close();
        if (debug) {
            System.out.print("Done\n");
        }
        //point.collect();
    }
}// CSBIGC class


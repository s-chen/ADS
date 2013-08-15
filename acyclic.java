
import java.io.*;
import java.util.*;
import java.lang.Math;

/**
 * An implementation of Algorithms for testing acylicity
 * and counting acyclic orientations of undirected graphs.
 */


public class acyclic {

    /** The method below will implement an Algorithm to
     * take a 2-dimensional square matrix representing a
     * directed graph, and determine whether that directed 
     * is acyclic (returning true) or not (returning false). **/

    public static boolean isDAG (boolean digraph[][]) { 
    	
    	int n = digraph.length;
    	boolean exists_sink = true;
    	int sink;
    	int no_edge_count = 0; 
    	boolean sink_array[] = new boolean[n]; // stores all sink vertices
    	boolean found_sink; // checks whether a sink has been found
    	
    	while (exists_sink) {
    		
    		found_sink = false;
    		
    		// Check for a sink in the digraph
    		for (int i = 0; i < n; i++) {
    			
    			no_edge_count = 0;
    			
    			for (int j = 0; j < n; j++) {	
    				if (digraph[i][j] == false) {
    					no_edge_count++;
    				} 
    			}
    			
    			// If all entries of a row of the matrix is false and the index i was not already a sink
    			// then assign index i to be the new sink
    			if (no_edge_count == n && sink_array[i] == false) {
    				
    				found_sink = true;
    				sink = i;
    				sink_array[i] = true;
    				
    				// Remove v -> sink from the graph
    				for (int v = 0; v < n; v++) {
    						digraph[v][sink] = false; 
    				}
    				break; 
    			} 
    		}
    		
    		if (!found_sink) {
    			exists_sink = false;	
    		}
    	}
    	
    	// If there exists an edge in the graph then graph is non-empty, graph is not acyclic otherwise
    	// graph is acyclic
    	for (int i = 0; i < n; i++) {
    		for (int j = 0; j < n; j++) {
    			if (digraph[i][j] == true) {
    				return false;
    			}
    		}
    	} 
    	return true;
    	
    
    }

    /** The method below will implement a simple algorithm
     * which takes an 2 dimensional matrix representing a 
     * undirected graph, and generates and returns a random
     * uniform orientation of that graph. **/
 
    public static boolean[][] uniformOrient(boolean[][] graph) {
    	
	
    	int n = graph.length;
    	boolean[][] digraph = new boolean[n][n];
    	boolean[][] is_edge_selected = new boolean[n][n];
    	
    	for (int i = 0; i < n; i++) {
    		for (int j = 0; j < n; j++) {
    			if (graph[i][j] == true && is_edge_selected[i][j] == false) {
				
    				// set is_edge_selected to be true when an edge of the graph has been selected
    				is_edge_selected[i][j] = true;
    				is_edge_selected[j][i] = true;

    				if (Math.random() > 0.5) {
    					digraph[i][j] = true;
    				} else {
    					digraph[j][i] = true;
    				}
    			}
			
    		}	
    	}
    	return digraph;
    	
    }

    
    /** The method below will implement a simple algorithm
     * which takes a (positive) integer n, and a probability
     * p and return a 2-dimensional matrix for an undirected
     * graph G on n vertices, generated according to the
     * random model G_{n,p}.  **/   
    
    public static boolean[][] erdosRenyi(int n, double p) {
    	
    	boolean[][] erdos_renyi_graph = new boolean[n][n];
    	
    	// Generate an undirected simple graph (no loops) with probability p
    	for (int i = 0; i < erdos_renyi_graph.length; i++) {
    		for (int j = 0; j < erdos_renyi_graph.length; j++) {
    			if (i < j) {
    				if (Math.random() <= p) {
    					erdos_renyi_graph[i][j] = true;
    					erdos_renyi_graph[j][i] = true;		
    				}
    			}
    		}
    	}
    	return erdos_renyi_graph;
    }
    
	 
	
    
    /** The method below will implement a dynamic programming 
     * algorithm to exactly evaluate the expected number of 
     * acyclic orientations in the random graph model G_{n,p}.
     * This algorithm should be based on the Robinson-Stanley
     * recurrence, and should run in O(n^2) time if possible.
     **/

    public static double expErdosRenyi(int n, double p) {
    	
    	double exp_num_acyclic_orientation;
    	
    	double base_case_A1 = 1; 
    	double sum = 0;
    	double[] array_A = new double[n+1]; // store each of A1, A2, ... , AN values evaluated at x = p/(1-p)
    	array_A[0] = base_case_A1; 
    	
    	// Compute A{n}(p/(1-p))
    	for (int j = 1; j <= n; j++) {
    		for (int i = 1; i <= j; i++) {
    			sum = sum + Math.pow((-1), i+1) * binomial_coefficient(j, i) * Math.pow((1+(p/(1-p))), i*(j-i)) * array_A[j-i];
    		}
    		array_A[j] = sum;
    		sum = 0;	
    	}
    	// E{n,p}[|AO(G)|] = (1-p)^(n choose 2) * A{n}(p/(1-p))
    	exp_num_acyclic_orientation = Math.pow((1-p), binomial_coefficient(n,2)) * array_A[n];
    	
    	return exp_num_acyclic_orientation;
    }
    
    
    // This method will compute the binomial coefficient (n,k)
    public static long binomial_coefficient(int n, int k) {
    	
    	long coefficient = 1;
    
    	for (int i = 1; i <= k; i++) {
    		coefficient *= n - (k-i);
    		coefficient /= i;
    	}
    	return coefficient;
    }
    

    /**
     * The following method should estimate the number of AOs
     * in G\in G_{n,p} over k graph trials where the graph
     * is drawn from G_{n,p} (Erdos-Renyi) random model and
     * 200 orientations-per-graph which are sampled uniformly
     * at random wrt the particular graph.  
     **/

    public static double estimErdosRenyi(int n, double p, int k) {  
    	
    	int count_acyclic_graph = 0;
    	int count_edges = 0;
    	double sum_ao_g_hat = 0;
    	double estimate_expected_ao_g;
    	boolean[][] random_undirected_graph = new boolean[n][n];
    	boolean[][] uniform_random_digraph = new boolean[n][n];
    	
    	for (int j = 0; j < k; j++) {
    		
    		count_acyclic_graph = 0;
    		count_edges = 0;
   
    		// Compute k samples of random undirected graphs
    		random_undirected_graph = erdosRenyi(n,p);
    
    		// Keep track of number of edges of the generated random undirected graph
    		for (int l = 0; l < random_undirected_graph.length; l++) {
    			for (int h = 0; h < random_undirected_graph.length; h++) {
    				if (random_undirected_graph[l][h]) {
    					count_edges++;
    				}
    			}
    		} 
    		count_edges = count_edges/2;
    		
    		// Compute k samples of 200 different uniform random orientations of directed graph from the undirected graph
    		for (int i = 1; i <= 200; i++) {
    			
    			uniform_random_digraph = uniformOrient(random_undirected_graph);
    			
    			if (isDAG(uniform_random_digraph)) {
    				count_acyclic_graph++;
    			}		
    		}
   
    		sum_ao_g_hat = sum_ao_g_hat + (Math.pow(2, count_edges)/200) * count_acyclic_graph;
    	}
    	estimate_expected_ao_g = sum_ao_g_hat / k;
    	 
    	return estimate_expected_ao_g;
    }

    /**
     * You should write a main method to run tests on your
     * different algorithms. 
     * 
     **/

    public static void main(String [] main) {
    	
    	// Test for isDAG 
    	//boolean test_diagraph_acyclic[][] = {{false, true, false}, {false, false, true}, {true, false, false}}; 
    	//System.out.println("Is graph directed acyclic: " + isDAG(test_diagraph_acyclic));
    	//System.out.println();
    	
    	 
    	// Test for uniformOrient
    	/*boolean[][] undirected_graph = {{false, true, false, false, false}, {true, false, false, true, false}, {false, false, false, true, true}, {false, true, true, false, false}, {false, false, true, false, false}};
    	
    	boolean[][] test_uniform_orient = uniformOrient(undirected_graph);
    	
    	System.out.println("The uniform random orientation of directed graph is:");
    	for (int i = 0; i < test_uniform_orient.length; i++) {
    		for (int j = 0; j < test_uniform_orient.length; j++) {
    			System.out.print(test_uniform_orient[i][j] + " ");
    			if (j == test_uniform_orient.length - 1) {
    				System.out.println();
    			}
    		}
    	}
    	System.out.println(); */
    	
    	// Test for erdosRenyi
    	/*boolean[][] test_erdos_renyi = erdosRenyi(3, 0.5);
    	
    	System.out.println("Random undirected graph generated by Erdos-Renyi model:");
    	for (int i = 0; i < test_erdos_renyi.length; i++) {
    		for (int j = 0; j < test_erdos_renyi.length; j++) {
    			System.out.print(test_erdos_renyi[i][j] + " ");
    			if (j == test_erdos_renyi.length - 1) {
    				System.out.println();
    			}
    		}
    	}
    	System.out.println(); */
    	
    	// Test for expErdosRenyi
    	//System.out.println("Expected number of acyclic orientations of the graph:");
    	//System.out.println(expErdosRenyi(10, 0.7));
    	//System.out.println();
    	
    	// Test for estimErdosRenyi
    	//System.out.println("Estimate of expected number of acyclic orientations:");
    	//System.out.println(estimErdosRenyi(10, 0.7, 1000));
    
    }
}

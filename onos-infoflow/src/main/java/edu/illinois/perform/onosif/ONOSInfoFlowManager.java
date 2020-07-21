package edu.illinois.perform.onosif;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import org.jgrapht.GraphPath;
import org.jgrapht.alg.shortestpath.DijkstraShortestPath;

import soot.G;
import soot.PackManager;
import soot.PatchingChain;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.MethodHandle;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.options.Options;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.ExceptionalBlockGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.Chain;
import soot.util.cfgcmd.CFGToDotGraph;
import soot.util.dot.DotGraph;

/**
 * ONOS Event Flow Static Analysis
 * @author benjaminujcich
 *
 */
public class ONOSInfoFlowManager {

	// list of API read method signatures
	public static final String API_READ_FILE = "apiReads.txt";
	// list of API write method signatures
	public static final String API_WRITE_FILE = "apiWrites.txt";
	// list of method signatures associated with data plane input
	public static final String DATA_PLANE_IN_FILE = "dataIn.txt";
	// list of method signatures associated with data plane output
	public static final String DATA_PLANE_OUT_FILE = "dataOut.txt";
	// directory where app binary (or apps binaries) reside(s)
	public static final String ONOS_APP_BINARY_ROOT_DIR = "onos-infoflow/bin/";
	// directory where ONOS implementation classes (Managers + Stores) live
	public static final String ONOS_IMPL_BINARY_ROOT_DIR = "onos-infoflow/bin-impl/";
	// directory where Java runtime lives
	public static final String JAVA_RUNTIME_ROOT_DIR = "java_rt/";
	
	// turn on benchmarking 
	public static final Boolean BENCHMARKING = false;
	
	public static void main(String[] args) {
		
		/*
		 * Set up event flow graph instantiation
		 */
		EFGraph efg = new EFGraph();
		
		/*
		 * Soot options
		 */
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);

		/*
		 * Assume that ONOS build has compiled everything to .class bytecode files,
		 * that the appropriate directory hierarchy is built (to match namespaces),
		 * and that they reside in this directory (e.g., bin/org/onosproject/...)
		 */
		List<String> appPaths = new ArrayList<String>();
		appPaths.add(ONOS_APP_BINARY_ROOT_DIR);
		appPaths.add(ONOS_IMPL_BINARY_ROOT_DIR);
		Options.v().set_process_dir(appPaths);
		
		/*
		 * Assume that Java runtime has been unzipped
		 */
		Options.v().set_soot_classpath(JAVA_RUNTIME_ROOT_DIR);
		Options.v().set_whole_program(true);
		Options.v().set_app(true);
		Options.v().setPhaseOption("cg", "safe-newinstance:true");
        Options.v().setPhaseOption("cg.cha","enabled:true");
        Options.v().setPhaseOption("cg.spark","enabled:false");
        Options.v().set_output_format(Options.output_format_jimple);
        Options.v().setPhaseOption("cg", "all-reachable:true");
        Options.v().setPhaseOption("jb","use-original-names:true");
                
        Scene.v().loadNecessaryClasses();

        /*
         * Load ONOS API method signatures from files
         */ 
        HashSet<String> apiReads = new HashSet<String>();
        FileInputStream fstream;
		try {
			fstream = new FileInputStream(API_READ_FILE);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
	        String strLine;
	        try {
				while ((strLine = br.readLine()) != null)   {
					apiReads.add(strLine);
				}
			} catch (IOException e) {
			}
	        fstream.close();
		} catch (FileNotFoundException e1) {
		} catch (IOException e) {
		}
		HashSet<String> apiWrites = new HashSet<String>();
		try {
	        fstream = new FileInputStream(API_WRITE_FILE);
	        BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;
	        try {
				while ((strLine = br.readLine()) != null)   {
					apiWrites.add(strLine);
				}
			} catch (IOException e) {
			}
	        fstream.close();
		} catch (FileNotFoundException e1) {
		} catch (IOException e) {
		}
        
		// structure to store what API calls get called
		HashSet<String> apiCalls = new HashSet<String>();
		// structure to store what event post()s get called
		HashSet<String> eventCalls = new HashSet<String>();
		
		/*
		 * Event listener/dispatcher maps
		 * 
		 * Maps event kind to a list of signatures of methods that care about it
		 * e.g. e.g. HostEvent --> [org.onosproject.net.host.... event(), ...]
		 * 
		 * Use this later on to tie the dispatchers to the listeners
		 */
		HashMap<String, Set<String>> eventListenerMap = new HashMap<String, Set<String>>();
		HashMap<String, Set<String>> eventDispatcherMap = new HashMap<String, Set<String>>();
		
		/* 
		 * Signatures of API reads and writes that have been found
		 */
		HashSet<String> apiWritesFound = new HashSet<String>();
		HashSet<String> apiReadsFound = new HashSet<String>();
		
		/*
		 * Benchmarking
		 * 		entry point name -> latency
		 */
		HashMap<String, Double> benchmarkEntryPoints = new HashMap<String, Double>();
		
        /*
         * PART 1:
         * Find all concrete event listener classes and determine which
         * methods are entry points. These include the following:
         *   * Events: EventListener.event() and EventListener.isRelevant()
         *   * Packets: PacketProcessor.process()
         */
    	System.out.printf("\n==== Part 1: Find all concrete event listener classes ====\n");
    	Stack<SootMethod> entryPoints = new Stack<SootMethod>();
        
        for (SootClass sc : Scene.v().getClasses()){
        	
        	//System.out.printf("%s\n", sc.getName());
        	
        	if ( sc.isConcrete() ) {	// ignore ifaces
        		if( sc.getInterfaceCount() > 0 ) {
        			// assume that the listener interface will follow pattern of ending in
        			// Listener, even if the concrete implementation class doesn't
        			for ( SootClass iface : sc.getInterfaces()) {
        				// only care about ONOS API listeners
        				if (iface.getName().startsWith("org.onosproject.net") && iface.getName().endsWith("Listener")) {
        					// assume that the methods of entry are Event.event() methods
        					for ( SootMethod sm : sc.getMethods() ) {
        						//if ( sm.getName().endsWith("event") || sm.getName().endsWith("isRelevant") ) {
        						if ( sm.getName().endsWith("event")) {
        							// avoid the generic Event and go for the subclassed Event
        							if (!sm.getSignature().contains("org.onosproject.event.Event")) {
        								entryPoints.push(sm);
        								// add to EFG
        								EFNode efgListener = new EFNode(sm.getSignature(), EFNodeType.EVENT_LISTENER, false);
        					        	efg.addNode(efgListener);
        					        	// add to event listener map
        					        	String eventKind = sm.getSignature().substring(sm.getSignature().indexOf("(") + 1, sm.getSignature().indexOf(")"));
        					        	if(eventListenerMap.containsKey(eventKind)) {
        					        		eventListenerMap.get(eventKind).add(sm.getSignature());
        					        	} else {
        					        		eventListenerMap.put(eventKind, new HashSet<String>());
        					        		eventListenerMap.get(eventKind).add(sm.getSignature());
        					        	}
        							}
        						}
        					}
        				} else if ( iface.getName().endsWith("Processor") ) {
        					for ( SootMethod sm : sc.getMethods() ) {
        						if ( sm.getName().endsWith("process") ) {
        							entryPoints.push(sm);
        							EFNode efgProcessor = new EFNode(sm.getSignature(), EFNodeType.PACKET_PROCESSOR, false);
    					        	efg.addNode(efgProcessor);
        						}
        					}
        				}
        			}
        		}
        	}
        }
        
        /* Clone entry point stack now so that we can do a graph search later */
        Stack<SootMethod> entryPointsGraphSearch = (Stack<SootMethod>) entryPoints.clone();
        
        System.out.printf("Event listener / packet processor entry points found: \n");
        for ( SootMethod sm : entryPoints ) {
        	System.out.printf("  %s\n", sm.toString());
        }
        System.out.printf("Event listener map: \n");
        for (Entry<String, Set<String>> entry : eventListenerMap.entrySet()) {
            String eventKind = entry.getKey();
            System.out.printf("  %s\n", eventKind);
            Set<String> sigs = entry.getValue();
            for (String sig : sigs) {
            	System.out.printf("    %s\n", sig);
            }
        }
        
        /*
         * PART 2:
         * Run analysis on each entry point separately
         */
        System.out.printf("\n==== Part 2: Analyze each entry point ====\n");

        HashMap<SootMethod, SootMethod> ifaceToImplMap = new HashMap<SootMethod, SootMethod>();
        HashMap<SootMethod, SootMethod> implToIface = new HashMap<SootMethod, SootMethod>();
        
        Set<SootMethod> entryPointsTraversed = new HashSet<SootMethod>();
        
        int methodsTraversedCount = 0;
        int entryPointsTraversedCount = 0;
        HashMap<SootMethod, Integer> methodsTraversedByEntryPointCount = new HashMap<SootMethod, Integer>();
        
        while (!entryPoints.isEmpty()) {
        	
        	SootMethod entryPoint = entryPoints.pop();
        
        	if (entryPoint == null) {
        		continue;
        	}
        	
        	// if we've traversed this, bail
        	if(entryPointsTraversed.contains(entryPoint)) {
        		continue;
        	}
        	
        	if (!BENCHMARKING) {
        		System.out.printf("Analyzing entry point %s...\n", entryPoint.getSignature().toString());
        	}
        	
        	entryPointsTraversedCount++;
        	methodsTraversedByEntryPointCount.put(entryPoint, 0);
        	
        	/*
        	 * Add representation of listener into EFG
        	 */
        	EFNode efgEntryPoint = efg.getNode(entryPoint.getSignature());
        	// if this is null, then this is an implementer, so get the interface
        	if (efgEntryPoint == null) {
        		efgEntryPoint = efg.getNode(implToIface.get(entryPoint).getSignature());
        	}
        	// if this is still null, then continue since we can't do anything
        	if (efgEntryPoint == null) {
        		continue;
        	}
        	
        	/* Start benchmark */
        	Long start = System.nanoTime();
        	
        	/*
        	 * Run soot packs
        	 */
        	Scene.v().setEntryPoints(new ArrayList<SootMethod>(Arrays.asList(entryPoint)));
        	PackManager.v().runPacks();
            //JimpleBasedInterproceduralCFG icfg = new JimpleBasedInterproceduralCFG();
            
            /*
             * Create a call graph manually
             * This is because soot doesn't handle lambda dynamic invocations
             * and creates false links in the call graph
             */
            Stack<SootMethod> methodsToCheck = new Stack<SootMethod>();
            Set<SootMethod> methodsTraversed = new HashSet<SootMethod>();
            methodsToCheck.push(entryPoint);
            
            while (!methodsToCheck.isEmpty()) {
            	SootMethod m = methodsToCheck.pop();
            	// if we've traversed this, bail
            	if(methodsTraversed.contains(m)) {
            		continue;
            	}
            	// if method doesn't have a body, bail
            	try {
            		m.getActiveBody();
            	} catch(Exception e) {
            		methodsTraversed.add(m);
            		continue;
            	}
            	
            	methodsTraversedCount++;
            	Integer methodsTraversedByEntryPointCountCount = methodsTraversedByEntryPointCount.get(entryPoint);
            	methodsTraversedByEntryPointCount.put(entryPoint, methodsTraversedByEntryPointCountCount + 1);
            	
            	//System.out.printf("%s\n", m.getSignature());
            	// method has a body and we haven't checked it yet
            	PatchingChain<Unit> uc = m.getActiveBody().getUnits();
            	// do any of these units invoke other methods?
            	for (Unit u : uc) {
            		//System.out.printf("    %s\n", u.toString());
            		SootMethod mInvoke = null;
            		
            		// AssignStmts will assign values upon return, so we need
        			// to get right-hand side of statement, check if it's invoking
        			// a relevant method, and then get that method
        			if (u instanceof AssignStmt) {
    					AssignStmt as = (AssignStmt) u;
    					if (as.getRightOp() instanceof InvokeExpr) {
    						InvokeExpr ie = (InvokeExpr) as.getRightOp();
    						if (ie instanceof DynamicInvokeExpr) {
    							DynamicInvokeExpr die = (DynamicInvokeExpr) ie;
    							// one of the args may be the method handle
    							for (Value arg : die.getBootstrapArgs()) {
    								if(arg instanceof MethodHandle) {
    									MethodHandle mh = (MethodHandle) arg;
    									// if we can't get this method, then bail
    									try {
    										mInvoke = Scene.v().getMethod(mh.getMethodRef().toString());
    									} catch(Exception e) {
    										mInvoke = null;
    									}
    								}
    							}
    						}
    						else {
    							mInvoke = ie.getMethod();
    						}
    					}
    				}
        			// InvokeStmts will invoke code without needing to return
        			else if (u instanceof InvokeStmt) {
        				InvokeStmt is = (InvokeStmt) u;
        				InvokeExpr ie = (InvokeExpr) is.getInvokeExpr();
        				if (ie instanceof DynamicInvokeExpr) {
        					DynamicInvokeExpr die = (DynamicInvokeExpr) ie;
        					for (Value arg : die.getBootstrapArgs()) {
        						if(arg instanceof MethodHandle) {
									MethodHandle mh = (MethodHandle) arg;
									// if we can't get this method, then bail
									try {
										mInvoke = Scene.v().getMethod(mh.getMethodRef().toString());
									} catch(Exception e) {
										mInvoke = null;
									}
								}
							}
						}
						else {
							mInvoke = ie.getMethod();
						}
        			}
        			
        			/* We have an invoked method, so now let's analyze it */
        			if (mInvoke != null) {
        				
        				/*
        				 * Methodology:
        				 * 		If invoked method is an interface *and* an API call:
        				 * 			Get its implementation method
        				 * 			Add its implementation method as an entry point
        				 * 			Do *not* add implementation method as a method to check (i.e., stop at the API boundary)
        				 * 		If invoked method is an interface but not an API call:
        				 * 			Get its implementation method
        				 * 			Add implementation method as a method to check (i.e., keep searching into the ICFG)
        				 * 		If invoked method relates to event dispatches:
        				 * 			Do nothing (i.e., stop at the boundary)
        				 */
        				
        				SootMethod implementer = null;
        				
        				// is this invoked method an interface? If so, we should see if any concrete methods implement it
        				if(!mInvoke.isConcrete()) {
        					// look through all soot classes that have concrete methods and some iface that they implement
        					for (SootClass sc : Scene.v().getClasses()){
        			        	if ( sc.isConcrete() ) {
        			        		if( sc.getInterfaceCount() > 0 ) {
        			        			for ( SootClass iface : sc.getInterfaces()) {
        			        				// does this iface have this method?
        			        				for ( SootMethod m1 : iface.getMethods() ) {
        			        					if (mInvoke.getSignature().equals(m1.getSignature())) {
													try {
														implementer = sc.getMethod(m1.getSubSignature());
														ifaceToImplMap.put(mInvoke, implementer);
					        							implToIface.put(implementer, mInvoke);
        			        						} catch (RuntimeException e) { 
        			        							implementer = null;
        			        						}
        			        					}
        			        				}
        			        			}
        			        		}
        			        	}
        			        }
        				}
        				
        				/* Is the invoked method an API write call? */
        				if (apiWrites.contains(mInvoke.getSignature())) {
        					if (!BENCHMARKING) {
        						System.out.printf("  Found a write (%s): %s\n", mInvoke.getName().toString(), mInvoke.getSignature());
        					}
							if(!apiWritesFound.contains(mInvoke.getSignature()) ) {
    							EFNode efgAPI = new EFNode(mInvoke.getSignature(), EFNodeType.API_METHOD, false);
    							efg.addNode(efgAPI);
    							apiWritesFound.add(mInvoke.getSignature());
    							if (implementer != null) {
        							entryPoints.push(implementer);
    							} else {
    								entryPoints.push(mInvoke);
    							}
    						}
    						EFNode efgAPI = efg.getNode(mInvoke.getSignature());
    						EFEdge edge = new EFEdge("W", EFEdgeType.WRITE, false);
        					efg.addEdge(efgEntryPoint, efgAPI, edge);
						}
        				
        				/* Is the invoked method an API read call? */
        				else if (apiReads.contains(mInvoke.getSignature())) {
        					if (!BENCHMARKING) {
        						System.out.printf("  Found a read (%s): %s\n", mInvoke.getName().toString(), mInvoke.getSignature());
        					}
							if(!apiReadsFound.contains(mInvoke.getSignature()) ) {
    							EFNode efgAPI = new EFNode(mInvoke.getSignature(), EFNodeType.API_METHOD, false);
    							efg.addNode(efgAPI);
    							apiReadsFound.add(mInvoke.getSignature());
    							if (implementer != null) {
        							entryPoints.push(implementer);
    							} else {
    								entryPoints.push(mInvoke);
    							}
    						}
    						EFNode efgAPI = efg.getNode(mInvoke.getSignature());
    						EFEdge edge = new EFEdge("R", EFEdgeType.READ, false);
    						efg.addEdge(efgAPI, efgEntryPoint, edge);
						}
        				
        				/* Is the invoked method related to a direct event dispatch? */
        				else if(mInvoke.getSignature().contains("Event") && 
								(mInvoke.getSignature().contains("post") || 
										mInvoke.getSignature().contains(" notifyDelegate(") || 
										mInvoke.getSignature().contains(" notify("))) {
        					if (!BENCHMARKING) {	
        						System.out.printf("  Found a direct event dispatch (%s): %s\n", mInvoke.getName().toString(), mInvoke.getSignature());        	
        					}
	        					/* add to event dispatcher map */
	        					String eventKind = mapToEventKind(entryPoint.getSignature());
					        	if(eventDispatcherMap.containsKey(eventKind)) {
					        		eventDispatcherMap.get(eventKind).add(entryPoint.getSignature());
					        	} else {
					        		eventDispatcherMap.put(eventKind, new HashSet<String>());
					        		eventDispatcherMap.get(eventKind).add(entryPoint.getSignature());
					        	}
	        			}
        				
        				/* Is the invoked method's implemented method related to 
        				 * something that relates to an event + store?  For now, 
        				 * treat these as effectively dispatching events */
        				else if(implementer != null && 
        						implementer.getSignature().contains("Event") && 
        						implementer.getSignature().contains("store")) {
        					if (!BENCHMARKING) {
	        					System.out.printf("  Found an indirect event dispatch (%s): %s\n", implementer.getName().toString(), implementer.getSignature());        	
        					}
	        					/* add to event dispatcher map */
	        					String eventKind = mapToEventKind(implementer.getSignature());
	        					
					        	if(eventDispatcherMap.containsKey(eventKind)) {
					        		//eventDispatcherMap.get(eventKind).add(entryPoint.getSignature());
					        		if( implToIface.get(entryPoint) != null  ) {
					        			eventDispatcherMap.get(eventKind).add(implToIface.get(entryPoint).getSignature());
					        		} else {
					        			eventDispatcherMap.get(eventKind).add(entryPoint.getSignature());
					        		}
					        	} else {
					        		eventDispatcherMap.put(eventKind, new HashSet<String>());
					        		if( implToIface.get(entryPoint) != null  ) {
					        			eventDispatcherMap.get(eventKind).add(implToIface.get(entryPoint).getSignature());
					        		} else {
					        			eventDispatcherMap.get(eventKind).add(entryPoint.getSignature());
					        		}
					        	}
	        			}
        				
        				/* Not an API call or event dispatch */
        				else {
        					// if we have an implementer method, check that; otherwise, add interface method
        					if (implementer != null) {
        						methodsToCheck.add(implementer);
        					} else {
        						methodsToCheck.add(mInvoke);
        					}
        				}
        				
        			}
        			
            	}
            	
            	// we've checked this method now
            	methodsTraversed.add(m);
            	
            }
            
            entryPointsTraversed.add(entryPoint);
            
            /* Stop benchmark */
            if (BENCHMARKING) {
        		Long stop = System.nanoTime();
        		Double totalSeconds = ((Long) (stop - start)).doubleValue() / 1000000000.0;
        		benchmarkEntryPoints.put(entryPoint.getSignature(), totalSeconds);
        	}
            
        }
        
        System.out.printf("Number of methods traversed: %s\n", methodsTraversedCount);
        System.out.printf("Number of entry points traversed: %s\n", entryPointsTraversedCount);
        
        System.out.printf("Method traversals per entry point: \n");
    	System.out.printf("\"ENTRY_POINT\",\"COUNT\"\n");
    	for (Entry<SootMethod, Integer> entry : methodsTraversedByEntryPointCount.entrySet()) {
    		String entryPointName = entry.getKey().getSignature();
    		Integer count = entry.getValue();
    		System.out.printf("\"%s\",%s\n", entryPointName, count);
    	}
        
        System.out.printf("Event dispatcher map: \n");
        for (Entry<String, Set<String>> entry : eventDispatcherMap.entrySet()) {
            String eventKind = entry.getKey();
            System.out.printf("  %s\n", eventKind);
            Set<String> sigs = entry.getValue();
            for (String sig : sigs) {
            	System.out.printf("    %s\n", sig);
            }
        }
        
        System.out.printf("API calls: \n");
        for ( String apiCall : apiCalls ) {
            System.out.printf("  %s\n", apiCall);
        }
        
        if (BENCHMARKING) {
        	System.out.printf("Benchmarking: \n");
        	System.out.printf("\"ENTRY_POINT\",\"TIME\"\n");
        	for (Entry<String, Double> entry : benchmarkEntryPoints.entrySet()) {
        		String entryPointName = entry.getKey();
        		Double latency = entry.getValue();
        		System.out.printf("\"%s\",%s\n", entryPointName, latency);
        	}
        }
        
        /*
         * PART 3:
         * Link dispatchers to the listeners
         */
        System.out.printf("\n==== Part 3: Link dispatchers to the listeners ====\n");
        for (Entry<String, Set<String>> entry : eventDispatcherMap.entrySet()) {
            String eventKind = entry.getKey();
            // if we don't have anything to dispatch to, then skip
            if(eventListenerMap.get(eventKind) == null) {
            	continue;
            }
            Set<String> eventListeners = eventListenerMap.get(eventKind);
            Set<String> eventDispatchers = entry.getValue();
            for (String listener : eventListeners) {
            	for (String dispatcher : eventDispatchers) {
            		EFNode efgListener = efg.getNode(listener);
            		EFNode efgDispatcher = efg.getNode(dispatcher);
            		EFEdge edge = new EFEdge(eventKind.substring(eventKind.lastIndexOf('.') + 1), EFEdgeType.EVENT, false);
            		if (efgListener != null && efgDispatcher != null) {
            			efg.addEdge(efgDispatcher, efgListener, edge);
            		} 
            	}
            }
        }
        
        
        /*
         * PART 4:
         * Link methods to data plane in
         */
        System.out.printf("\n==== Part 4: Link methods to data plane in ====\n");
        EFNode efgDataPlaneIn = new EFNode("Incoming data from data plane", EFNodeType.DATA_PLANE_IN, false);
    	efg.addNode(efgDataPlaneIn);
    	HashSet<String> dataPlaneIns = new HashSet<String>();
		try {
			fstream = new FileInputStream(DATA_PLANE_IN_FILE);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
	        String strLine;
	        try {
				while ((strLine = br.readLine()) != null)   {
					dataPlaneIns.add(strLine);
				}
			} catch (IOException e) {
			}
	        fstream.close();
		} catch (FileNotFoundException e1) {
		} catch (IOException e) {
		}
		for (String dataPlaneIn : dataPlaneIns ) {
			if (efg.getNode(dataPlaneIn) != null) {
				EFNode node = efg.getNode(dataPlaneIn);
				efg.addEdge(efgDataPlaneIn, node, new EFEdge("", EFEdgeType.DATA_PLANE_IN, false));
			}
		}
        
		
        /*
         * PART 5:
         * Link methods to data plane out
         */
		System.out.printf("\n==== Part 5: Link methods to data plane out ====\n");
    	EFNode efgDataPlaneOut = new EFNode("Outgoing data to data plane", EFNodeType.DATA_PLANE_OUT, false);
    	efg.addNode(efgDataPlaneOut);
    	HashSet<String> dataPlaneOuts = new HashSet<String>();
		try {
			fstream = new FileInputStream(DATA_PLANE_OUT_FILE);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
	        String strLine;
	        try {
				while ((strLine = br.readLine()) != null)   {
					dataPlaneOuts.add(strLine);
				}
			} catch (IOException e) {
			}
	        fstream.close();
		} catch (FileNotFoundException e1) {
		} catch (IOException e) {
		}
		for (String dataPlaneOut : dataPlaneOuts ) {
			if (efg.getNode(dataPlaneOut) != null) {
				EFNode node = efg.getNode(dataPlaneOut);
				efg.addEdge(node, efgDataPlaneOut, new EFEdge("", EFEdgeType.DATA_PLANE_OUT, false));
			}
		}
        
		
        
        
        
        /*
         * PART 6:
         * Event flow graph traversals
         * 
         * Methodology:
         * 		For each NODE we care about (probably an event listener):
         * 			Run Dijkstra's algorithm from efgDataPlaneIn -> NODE
         * 				Does a path exist? If yes, good.
         * 			Run Dijkstra's algorithm from NODE -> efgDataPlaneOut
         * 				Does a path exist? If yes, good.
         * 		For each other NODE with the same Event type (approx. present context):
         * 			Repeat above; if good, then add to context
         * 		For each other NODE without the same Event type (approx absent context):
         * 			Repeat above; if good, then add to context
         */
        
		System.out.printf("\n==== Part 6: Event flow graph path traversals ====\n");
        for (SootMethod entryPoint : entryPointsGraphSearch) {
        	
        	String entryPointName = entryPoint.getSignature();
        	EFNode efgEntryPointNode = efg.getNode(entryPointName);
        	
        	if (efg.pathExists(efgDataPlaneIn, efgEntryPointNode) &&
        			efg.pathExists(efgEntryPointNode, efgDataPlaneOut)) {
        		System.out.printf("%s\n", entryPointName);
        		System.out.printf("  V: %s\n", efg.getPathNodes(efgDataPlaneIn, efgEntryPointNode));
        		System.out.printf("  E: %s\n", efg.getPathEdges(efgDataPlaneIn, efgEntryPointNode));
        		System.out.printf("  V: %s\n", efg.getPathNodes(efgEntryPointNode, efgDataPlaneOut));
        		System.out.printf("  E: %s\n", efg.getPathEdges(efgEntryPointNode, efgDataPlaneOut));
        	}
        	
        	
        }
        
        /*
         * PART 7:
         * Create the event flow graph
         */
		System.out.printf("\n==== Part 7: Create the visual event flow graph ====\n");
        efg.pp();
        efg.cleanSingleNodes();
        efg.generateDot();
        
        
                
	}
	
	/**
	 * Convert an API service inferface method to an implementation method
	 * @param signature
	 * @param classes
	 * @return
	 */
	private static SootMethod convertIfaceToImpl(String signature, Chain<SootClass> classes) {
		
		SootMethod implementer = null;
        for (SootClass sc : classes){
        	
        	if ( sc.isConcrete() ) {
        		if( sc.getInterfaceCount() > 0 ) {
        			for ( SootClass iface : sc.getInterfaces()) {
        				
        				for ( SootMethod m : iface.getMethods() ) {
        					if (signature.equals(m.getSignature())) {
        						try {
        							implementer = sc.getMethod(m.getSubSignature());
        						} catch (RuntimeException e) { 
        							implementer = null;
        						}
        						
        						//System.out.printf("%s\n", sc.getMethods());
        						//for (SootMethod mm : sc.getMethods()) {
        						//	System.out.printf(" %s\n", mm.getSubSignature());
        						//}
        						//apiEntryPoints.add(sc.getMethod(m.getName()));
        						//System.out.printf("iface: %s, method: %s\n", iface.getName(), m.getSignature().toString());
        					}
        				}
        				
        				
        			}
        		}
        	}
        }
        
        return implementer;

	}

	
	/**
	 * Maps the likely manager to the likely kind of event
	 * @param sig
	 * @return
	 */
	public static String mapToEventKind(String sig) {
		if (sig.startsWith("<org.onosproject.net.host") || sig.startsWith("<org.onosproject.store.host")) {
			return "org.onosproject.net.host.HostEvent";
		} else if (sig.startsWith("<org.onosproject.net.topology") || sig.startsWith("<org.onosproject.store.topology")) {
			return "org.onosproject.net.topology.TopologyEvent";
		} else if (sig.startsWith("<org.onosproject.net.intent") || sig.startsWith("<org.onosproject.store.intent")) {
			return "org.onosproject.net.intent.IntentEvent";
		} else if (sig.startsWith("<org.onosproject.net.resource") || sig.startsWith("<org.onosproject.store.resource")) {
			return "org.onosproject.net.resource.ResourceEvent";
		} else if (sig.startsWith("<org.onosproject.net.link") || sig.startsWith("<org.onosproject.store.link")) {
			return "org.onosproject.net.link.LinkEvent";
		} else if (sig.startsWith("<org.onosproject.net.device") || sig.startsWith("<org.onosproject.store.device")) {
			return "org.onosproject.net.device.DeviceEvent";
		} else if (sig.startsWith("<org.onosproject.net.config") || sig.startsWith("<org.onosproject.store.config")) {
			return "org.onosproject.net.config.NetworkConfigEvent";
		} else if (sig.startsWith("<org.onosproject.net.flow.oldbatch") || sig.startsWith("<org.onosproject.store.flow.oldbatch")) {
			return "org.onosproject.net.flow.oldbatch.FlowRuleBatchEvent";
		} else if (sig.startsWith("<org.onosproject.net.flow") || sig.startsWith("<org.onosproject.store.flow")) {
			return "org.onosproject.net.flow.FlowRuleEvent";
		} else if (sig.startsWith("<org.onosproject.net.driver") || sig.startsWith("<org.onosproject.store.driver")) {
			return "org.onosproject.net.driver.DriverEvent";
		} else if (sig.startsWith("<org.onosproject.net.meter") || sig.startsWith("<org.onosproject.store.meter")) {
			return "org.onosproject.net.meter.MeterEvent";
		} else if (sig.startsWith("<org.onosproject.net.flowobjective") || sig.startsWith("<org.onosproject.store.flowobjective")) {
			return "org.onosproject.net.flowobjective.ObjectiveEvent";
		} else if (sig.startsWith("<org.onosproject.net.group") || sig.startsWith("<org.onosproject.store.group")) {
			return "org.onosproject.net.group.GroupEvent";
		} else if (sig.startsWith("<org.onosproject.net.edgeservice") || sig.startsWith("<org.onosproject.store.edgeservice")) {
			return "org.onosproject.net.edge.EdgePortEvent";
		} else if (sig.startsWith("<org.onosproject.net.pi") || sig.startsWith("<org.onosproject.store.pi")) {
			return "org.onosproject.net.pi.service.PiPipeconfEvent";
		} else if (sig.startsWith("<org.onosproject.net.packet")) {
			return "org.onosproject.net.packet.PacketEvent";
		} 
		System.out.printf("NOT FOUND: %s\n", sig);
		// fallback to org.onosproject.event.Event
		return "org.onosproject.event.Event";
	}

}

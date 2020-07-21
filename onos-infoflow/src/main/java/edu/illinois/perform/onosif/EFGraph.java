package edu.illinois.perform.onosif;

import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.regex.Pattern;
import java.util.regex.Matcher;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;

import org.jgrapht.GraphPath;
import org.jgrapht.alg.shortestpath.DijkstraShortestPath;
import org.jgrapht.graph.DirectedMultigraph;
import org.jgrapht.io.Attribute;
import org.jgrapht.io.ComponentAttributeProvider;
import org.jgrapht.io.ComponentNameProvider;
import org.jgrapht.io.DOTExporter;
import org.jgrapht.io.DefaultAttribute;
import org.jgrapht.io.ExportException;
import org.jgrapht.io.GraphExporter;

/**
 * Event flow graph that represents an abstracted view of event (data/control)
 * flow in the SDN control plane. Implemented with JGraphT.
 */
public class EFGraph {

	public static final Boolean LARGE_GRAPH = true;	// omit labels for large graphs
	private DirectedMultigraph<EFNode, EFEdge> g;	// JGraphT representation of graph
	
	public EFGraph() {
		this.g = new DirectedMultigraph<EFNode, EFEdge>(null);
	}
	
	/**
	 * Add node to event flow graph
	 * @param node
	 */
	public void addNode(EFNode node) {
		g.addVertex(node);
	}
	
	/**
	 * Return node by name
	 * @param name
	 * @return node or null
	 */
	public EFNode getNode(String name) {
		for ( EFNode node : g.vertexSet()) {
			if(node.getName().equals(name)) {
				return node;
			}
		}
		return null;
	}
	
	/**
	 * Add edge between two nodes in event flow graph
	 * @param from
	 * @param to
	 * @param edge
	 */
	public void addEdge(EFNode from, EFNode to, EFEdge edge) {
		// don't allow loops
		if(from.getName().equals(to.getName())) {
			return;
		}
		// FIXME: for now, prevent duplicate edges
		// may want to adjust this if we want to have multiple event types as multi-edges
		if(!g.containsEdge(from, to)) {
			g.addEdge(from, to, edge);
		}
	}
	
	/**
	 * Connect dispatchers with listeners
	 */
	public void connectEventDispatchersListeners() {
		
	}
	
	/**
	 * Check whether path exists between two nodes
	 * @param src
	 * @param dst
	 * @return
	 */
	public Boolean pathExists(EFNode src, EFNode dst) {
		GraphPath<EFNode, EFEdge> path = DijkstraShortestPath.findPathBetween(g, src, dst);
		if (path != null) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Return a string representation of the path edges, if it exists
	 * @param src
	 * @param dst
	 * @return
	 */
	public String getPathEdges(EFNode src, EFNode dst) {
		GraphPath<EFNode, EFEdge> path = DijkstraShortestPath.findPathBetween(g, src, dst);
		if (path != null) {
			return path.getEdgeList().toString();
		} else {
			return null;
		}
	}
	
	/**
	 * Return a string representation of the path vertices, if it exists
	 * @param src
	 * @param dst
	 * @return
	 */
	public String getPathNodes(EFNode src, EFNode dst) {
		GraphPath<EFNode, EFEdge> path = DijkstraShortestPath.findPathBetween(g, src, dst);
		if (path != null) {
			return path.getVertexList().toString();
		} else {
			return null;
		}
	}
	
	/**
	 * Pretty print information about event flow graph
	 */
	public void pp() {
		System.out.printf("\n==== Event flow graph details: ====\n");
		
		System.out.printf("\nEFG nodes:\n");
		for ( EFNode node : g.vertexSet()) {
			System.out.printf("  %s\n", node.toString());
		}
		
		System.out.printf("\n");
	}
	
	/**
	 * Construct visual representation of event flow graph with Graphviz
	 */
	public void generateDot() {
		
		/* Node identifier */
		ComponentNameProvider<EFNode> nodeIdProvider = new ComponentNameProvider<EFNode>()
        {
            public String getName(EFNode node)
            {
            	// dot langauge doesn't like IDs starting with number, so append some
            	// string characters at start
                return "node" + node.getUuid().toString().replace("-", "");
            }
        };
        /* Node text label */
        ComponentNameProvider<EFNode> nodeLabelProvider = new ComponentNameProvider<EFNode>()
        {
            public String getName(EFNode node)
            {
            	// FIXME: adjust label to be smaller
                //return node.getName().replace(":", "\n").replace("<", "").replace(">", "");
            	
            	if (LARGE_GRAPH) {
            		if (node.getNodeType() == EFNodeType.DATA_PLANE_IN) {
                		return "Data Plane\nIn";
                	}
                	else if (node.getNodeType() == EFNodeType.DATA_PLANE_OUT) {
                		return "Data Plane\nOut";
                	}
                	else if (node.getNodeType() == EFNodeType.API_METHOD) {
                		String text = node.getName();
                		String patternString1 = "(<org.onosproject.)(.*)(: )(.*)( )(.*)(\\()(.*)";
                        Pattern pattern = Pattern.compile(patternString1);
                        Matcher matcher = pattern.matcher(text);
                        matcher.matches();
                        String string = matcher.group(2);
                        return string.substring(string.lastIndexOf('.') + 1) + "\n" + matcher.group(6) + "(...)";
                    }
                	else if (node.getNodeType() == EFNodeType.PACKET_PROCESSOR 
                			|| node.getNodeType() == EFNodeType.EVENT_LISTENER) {
                		String text = node.getName();
                		String patternString1 = "(<org.onosproject.)(.*)(:)(.*)";
                        Pattern pattern = Pattern.compile(patternString1);
                        Matcher matcher = pattern.matcher(text);
                        matcher.matches();
                        String string = matcher.group(2).replace("$", "\n");
                        return string.substring(0, string.lastIndexOf('.')) + "\n" + string.substring(string.lastIndexOf('.') + 1);
                	}
            		return "";
            	}
            	// FIXME: make this more readable somehow
            	else {
            		if (node.getNodeType() == EFNodeType.DATA_PLANE_IN) {
                		return "Data Plane In";
                	}
                	else if (node.getNodeType() == EFNodeType.DATA_PLANE_OUT) {
                		return "Data Plane Out";
                	}
                	else if (node.getNodeType() == EFNodeType.API_METHOD) {
                		// FIXME
                		return node.getName().replace(":", "\n").replace("<", "").replace(">", "");
                	}
                	else if (node.getNodeType() == EFNodeType.PACKET_PROCESSOR) {
                		// FIXME
                		return node.getName().replace(":", "\n").replace("<", "").replace(">", "");
                	}
                	else if (node.getNodeType() == EFNodeType.EVENT_LISTENER) {
                		// FIXME
                		return node.getName().replace(":", "\n").replace("<", "").replace(">", "");
                	}
            		return "";
            	}
            	
            }
        };
        /* Edge text label */
        ComponentNameProvider<EFEdge> edgeLabelProvider = new ComponentNameProvider<EFEdge>()
        {
            public String getName(EFEdge edge)
            {
            	return "";
                //return edge.getName();
            	/*if (edge.getEdgeType() == EFEdgeType.EVENT) {
            		return edge.getName();
            	}
            	else {
            		return "";
            	}*/
            }
        };
        /* Node attributes */
        ComponentAttributeProvider<EFNode> nodeAttributeProvider = new ComponentAttributeProvider<EFNode>()
        {
			public Map<String, Attribute> getComponentAttributes(EFNode node) {
				Map<String, Attribute> map = new LinkedHashMap<String, Attribute>();
				map.put("margin", DefaultAttribute.createAttribute("0.05"));
				map.put("fontname", DefaultAttribute.createAttribute("Linux Biolinum"));
				if (node.getNodeType() == EFNodeType.EVENT_LISTENER || node.getNodeType() == EFNodeType.PACKET_PROCESSOR) {
					map.put("shape", DefaultAttribute.createAttribute("box"));
					map.put("style", DefaultAttribute.createAttribute("filled"));
					map.put("penwidth", DefaultAttribute.createAttribute("2"));
					map.put("fillcolor", DefaultAttribute.createAttribute("#bdd8ed"));
					map.put("fontsize", DefaultAttribute.createAttribute("18"));
				}
				else if (node.getNodeType() == EFNodeType.API_METHOD) {
					map.put("shape", DefaultAttribute.createAttribute("ellipse"));
					map.put("style", DefaultAttribute.createAttribute("filled"));
					map.put("fillcolor", DefaultAttribute.createAttribute("#efefef"));
					map.put("fontsize", DefaultAttribute.createAttribute("18"));
				}
				else if (node.getNodeType() == EFNodeType.DATA_PLANE_IN || node.getNodeType() == EFNodeType.DATA_PLANE_OUT) {
					map.put("shape", DefaultAttribute.createAttribute("box"));
					map.put("style", DefaultAttribute.createAttribute("filled"));
					map.put("fillcolor", DefaultAttribute.createAttribute("#ffffff"));
					map.put("fontsize", DefaultAttribute.createAttribute("24"));
				}
				return map;
			}
        };
        /* Edge attributes 
         * FIXME: according to type */
        ComponentAttributeProvider<EFEdge> edgeAttributeProvider = new ComponentAttributeProvider<EFEdge>()
        {
			public Map<String, Attribute> getComponentAttributes(EFEdge edge) {
				Map<String, Attribute> map = new LinkedHashMap<String, Attribute>();
				map.put("fontname", DefaultAttribute.createAttribute("Linux Biolinum"));
				map.put("fontsize", DefaultAttribute.createAttribute("18"));
				if (edge.getEdgeType() == EFEdgeType.EVENT) {
					map.put("penwidth", DefaultAttribute.createAttribute("2"));
				}
				else if (edge.getEdgeType() == EFEdgeType.READ || edge.getEdgeType() == EFEdgeType.WRITE ) {
					map.put("style", DefaultAttribute.createAttribute("dashed"));
					map.put("penwidth", DefaultAttribute.createAttribute("1.25"));
				}
				else if (edge.getEdgeType() == EFEdgeType.DATA_PLANE_IN || edge.getEdgeType() == EFEdgeType.DATA_PLANE_OUT) {
					map.put("penwidth", DefaultAttribute.createAttribute("1.25"));
				}
				return map;
			}
        };
        
        /*
         * Plot nodes and edges
         */
        GraphExporter<EFNode, EFEdge> exporter = new DOTExporter<EFNode, EFEdge>(nodeIdProvider, nodeLabelProvider, edgeLabelProvider, nodeAttributeProvider, edgeAttributeProvider);
        try {
        	// write out to DOT
        	System.out.printf("Writing out event flow graph DOT file...\n");
			FileWriter fw = new FileWriter("event-flow-graph.dot");
			Writer writer = new StringWriter();
			/* graph-wide attributes */
			if (LARGE_GRAPH) {
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("ratio", "compress");
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("nodesep", "0.2");
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("ranksep", "1");
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("margin", "0");
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("rankdir", "LR");
			}
			else {
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("ratio", "compress");
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("nodesep", "0.2");
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("ranksep", "0.4");
				((DOTExporter<EFNode, EFEdge>) exporter).putGraphAttribute("margin", "0");
			}
			exporter.exportGraph(g, writer);
			fw.write(writer.toString());
			fw.close();
			// write out to PDF
			System.out.printf("Writing out event flow graph PDF file...\n");
			String stringExec = "dot -Tpdf event-flow-graph.dot -o event-flow-graph.pdf";
			Runtime.getRuntime().exec(new String[] { "bash", "-c", stringExec });
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (ExportException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
       
		
	}

	/**
	 * Remove nodes from graph that aren't connected to anything else
	 */
	public void cleanSingleNodes() {
		// TODO Auto-generated method stub
		
		HashSet<EFNode> setToRemove = new HashSet<EFNode>();
		for ( EFNode node : g.vertexSet()) {
			if(g.edgesOf(node).size() == 0) {
				setToRemove.add(node);
			}
		}
		for (EFNode node : setToRemove) {
			g.removeVertex(node);
		}
		
	}
	
	
}

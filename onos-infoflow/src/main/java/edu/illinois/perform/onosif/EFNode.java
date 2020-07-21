package edu.illinois.perform.onosif;

import java.util.UUID;

/**
 * Event flow graph node
 */
public class EFNode {

	private UUID uuid;
	private String name;
	private EFNodeType nodeType;
	private Boolean relevant;

	public EFNode(String name, EFNodeType nodeType, Boolean relevant) {
		this.setUuid(UUID.randomUUID());
		this.name = name;
		this.nodeType = nodeType;
		this.relevant = relevant;
	}
	
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public EFNodeType getNodeType() {
		return nodeType;
	}

	public void setNodeType(EFNodeType nodeType) {
		this.nodeType = nodeType;
	}

	/**
	 * Is this node relevant for our event flow analysis?
	 * @return true or false
	 */
	public Boolean isRelevant() {
		return relevant;
	}

	public void setRelevant(Boolean relevant) {
		this.relevant = relevant;
	}
	
	@Override
	public String toString() {
		return "EFNode [name=" + name + ", nodeType=" + nodeType + "]";
	}

	public UUID getUuid() {
		return uuid;
	}

	public void setUuid(UUID uuid) {
		this.uuid = uuid;
	}
	
}

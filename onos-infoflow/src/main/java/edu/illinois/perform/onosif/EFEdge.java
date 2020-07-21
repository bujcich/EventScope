package edu.illinois.perform.onosif;

import java.util.UUID;

/**
 * Event flow graph edge
 */
public class EFEdge {

	private UUID uuid;
	private String name;
	private EFEdgeType edgeType;
	private Boolean relevant;

	public EFEdge(String name, EFEdgeType edgeType, Boolean relevant) {
		this.setUuid(UUID.randomUUID());
		this.name = name;
		this.edgeType = edgeType;
		this.relevant = relevant;
	}
	
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public EFEdgeType getEdgeType() {
		return edgeType;
	}

	public void setEdgeType(EFEdgeType edgeType) {
		this.edgeType = edgeType;
	}

	/**
	 * Is this edge relevant for our event flow analysis?
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
		return "EFEdge [name=" + name + ", edgeType=" + edgeType + "]";
	}

	public UUID getUuid() {
		return uuid;
	}

	public void setUuid(UUID uuid) {
		this.uuid = uuid;
	}
	
}

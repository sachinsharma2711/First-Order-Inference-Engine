package fol;

import java.util.HashMap;

public class Node {
	private String value;
	private boolean negated;
	private boolean connector;

	public Node left;
	public Node right;

	private static final HashMap<String, String> complementOperator;
	static {
		complementOperator = new HashMap<String, String>();
		complementOperator.put("&", "|");
		complementOperator.put("|", "&");
	}

	public Node(String value, boolean isConnector) {
		this.value = value;
		this.negated = false;
		this.connector = isConnector;
		this.left = null;
		this.right = null;
	}

	public String getValue() {
		return this.value;
	}

	public void setValue(String value) {
		this.value = value;
	}

	public boolean isConnector() {
		return this.connector;
	}

	public boolean isNegated() {
		return this.negated;
	}

	public void negate() {
		if (this.connector) {
			this.value = complementOperator.get(this.value);
		} else {
			this.negated = !this.negated;
		}
	}
}

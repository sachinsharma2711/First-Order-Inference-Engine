package fol;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import fol.folParser.SentenceContext;

public class FirstOrderInferenceEngine {
	private static ArrayList<ArrayList<String>> kb;
	private static HashMap<String, ArrayList<Integer>> literal2SentencesMap;
	private static ArrayList<String> queries;

	public static void main(String[] args) {
		kb = new ArrayList<ArrayList<String>>();
		literal2SentencesMap = new HashMap<String, ArrayList<Integer>>();
		queries = new ArrayList<String>();
		BufferedReader br = null;
		try {
			br = new BufferedReader(new FileReader("input.txt"));

			int numberOfQueries = Integer.parseInt(br.readLine().trim());
			for (int i = 0; i < numberOfQueries; i++) {
				queries.add(br.readLine().trim());
			}
			int kbSize = Integer.parseInt(br.readLine().trim());
			for (int i = 0; i < kbSize; i++) {
				ANTLRInputStream input = new ANTLRInputStream(br.readLine().trim());

				folLexer lexer = new folLexer(input);

				CommonTokenStream tokens = new CommonTokenStream(lexer);

				folParser parser = new folParser(tokens);
				
				SentenceContext context = parser.sentence();
				
				Node node = removeImplicationAndMoveNegationInwards(context);
				node = distributeANDOverOR(node);
				inorder(node);
				add2KB(node);
			}
			PrintWriter writer = new PrintWriter("output.txt", "UTF-8");
			for (String query : queries) {
				String[] str = query.split("[ \t]");
				query = String.join("", str);
				System.out.println(query);
				boolean queryResult = folResolution(query);
				writer.println(String.valueOf(queryResult).toUpperCase());
			}
			writer.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (NumberFormatException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private static boolean folResolution(String query) {
		ArrayList<ArrayList<String>> newKB = new ArrayList<ArrayList<String>>();
		HashSet<HashSet<String>> workingSet = new HashSet<HashSet<String>>();

		for (ArrayList<String> sentence : kb) {
			ArrayList<String> sentenceCopy = new ArrayList<String>(sentence);
			newKB.add(sentenceCopy);
		}
		HashMap<String, ArrayList<Integer>> newLiteral2SentencesMap = new HashMap<String, ArrayList<Integer>>();

		for (Entry<String, ArrayList<Integer>> entry : literal2SentencesMap.entrySet()) {
			ArrayList<Integer> valueCopy = new ArrayList<Integer>(entry.getValue());
			newLiteral2SentencesMap.put(entry.getKey(), valueCopy);
		}
		ArrayList<String> s = new ArrayList<String>();
		if (query.charAt(0) != '~') {
			s.add("~" + query);
		} else {
			s.add(query.substring(1));
		}
		newKB.add(s);
		String q = s.get(0).split("\\(")[0];
		ArrayList<Integer> map = newLiteral2SentencesMap.get(q);
		if (map == null) {
			map = new ArrayList<Integer>();
		}
		map.add(newKB.size() - 1);
		newLiteral2SentencesMap.put(q, map);
		while (true) {
			HashSet<UnorderedPair<ArrayList<String>>> pairs = new HashSet<UnorderedPair<ArrayList<String>>>();
			for (int i = 0; i < newKB.size(); i++) {
				ArrayList<String> sentence1 = newKB.get(i);
				for (String clause : sentence1) {
					String c;
					if (clause.charAt(0) == '~') {
						c = clause.substring(1);
					} else {
						c = "~" + clause;
					}
					c = c.split("\\(")[0];
					ArrayList<Integer> listOfSentenceIndices = newLiteral2SentencesMap.get(c);
					if (listOfSentenceIndices != null) {
						for (Integer a : listOfSentenceIndices) {
							if (a.intValue() > i) {
								pairs.add(new UnorderedPair<ArrayList<String>>(sentence1, newKB.get(a.intValue())));
							}
						}
					}
				}
			}
			for (UnorderedPair<ArrayList<String>> pair : pairs) {
				ArrayList<String> resolvents = resolve(pair.getFirst(), pair.getSecond());
				if (!resolvents.isEmpty()) {
					if (resolvents.get(0).equals("False")) {
						return true;
					}
					workingSet.add(new HashSet<String>(resolvents));
				}
			}
			Set<HashSet<String>> clauses = new HashSet<HashSet<String>>();
			for(ArrayList<String> ss : newKB){
				HashSet<String> sentence = new HashSet<String>(ss);
				clauses.add(sentence);
			}
			
			if(workingSet.size()>4000){
				return false;
			}
			workingSet.removeAll(clauses);
			if (workingSet.isEmpty() ) {
				return false;
			}
			for (HashSet<String> c : workingSet) {
				for (String t : c) {
					q = t.split("\\(")[0];
					ArrayList<Integer> m = newLiteral2SentencesMap.get(q);
					if (m == null) {
						m = new ArrayList<Integer>();
					}
					m.add(newKB.size());
					newLiteral2SentencesMap.put(q, m);
				}
				newKB.add(new ArrayList<String>(c));
			}
		}
	}

	private static ArrayList<String> resolve(ArrayList<String> sentence1, ArrayList<String> sentence2) {
		ArrayList<String> resolvents = new ArrayList<String>();
		ArrayList<String> s1 = new ArrayList<String>(sentence1);
		ArrayList<String> s2 = new ArrayList<String>(sentence2);

		for (String disjunct1 : s1) {
			for (String disjunct2 : s2) {
				HashMap<String, String> theta = new HashMap<String, String>();
				if (disjunct1.charAt(0) == '~') {
					theta = unify(disjunct1.substring(1), disjunct2, theta);
				} else if(disjunct2.charAt(0) == '~') {
					theta = unify(disjunct1, disjunct2.substring(1), theta);
				}
				if (theta != null) {
					disjunct1 = substitute(disjunct1, theta);
					disjunct2 = substitute(disjunct2, theta);
					if (disjunct1.equals("~" + disjunct2) || disjunct2.equals("~" + disjunct1)) {
						for (int i = 0; i < s1.size(); i++) {
							s1.set(i, substitute(s1.get(i), theta));
						}
						for (int i = 0; i < s2.size(); i++) {
							s2.set(i, substitute(s2.get(i), theta));
						}
						HashSet<String> dnew = new HashSet<String>();
						for (String disjunct : s1) {
							if (!disjunct.equals(disjunct1)) {
								dnew.add(disjunct);
							}
						}
						for (String disjunct : s2) {
							if (!disjunct.equals(disjunct2)) {
								dnew.add(disjunct);
							}
						}
						if (dnew.isEmpty()) {
							resolvents.add(0, "False");
						} else {
							resolvents.addAll(dnew);
						}
					}
				}
			}
		}
		return resolvents;
	}

	private static String substitute(String disjunct, HashMap<String, String> theta) {
		String[] predicate = disjunct.split("\\(");
		String argList = predicate[1].substring(0, predicate[1].length() - 1);
		String[] args = argList.split(",");
		for (int i = 0; i < args.length; i++) {
			String sub = theta.get(args[i]);
			if (args[i].matches("[a-z][0-9]+") && sub != null) {
				args[i] = sub;
			}
		}
		argList = String.join(",", args);
		predicate[1] = argList + ")";
		disjunct = String.join("(", predicate);
		return disjunct;
	}

	private static HashMap<String, String> unify(String x, String y, HashMap<String, String> theta) {
		if (theta == null) {
			return null;
		} else if (x.equals(y)) {
			return theta;
		} else if (x.matches("[a-z][0-9]+")) {
			return unifyVar(x, y, theta);
		} else if (y.matches("[a-z][0-9]+")) {
			return unifyVar(y, x, theta);
		} else {
			String[] a = x.split("\\(");
			String[] b = y.split("\\(");
			if (a.length > 1 && b.length > 1) {
				String[] xArgs = a[1].substring(0, a[1].length() - 1).split(",");
				String[] yArgs = b[1].substring(0, b[1].length() - 1).split(",");
				return unify(String.join(",", xArgs), String.join(",", yArgs), unify(a[0], b[0], theta));
			} else {
				String[] xArgs = a[0].split(",");
				String[] yArgs = b[0].split(",");
				if (xArgs.length > 1 && yArgs.length > 1 && xArgs.length == yArgs.length) {
					return unify(String.join(",", xArgs).substring(xArgs[0].length() + 1),
							String.join(",", yArgs).substring(yArgs[0].length() + 1), unify(xArgs[0], yArgs[0], theta));
				}
			}
		}
		return null;
	}

	private static HashMap<String, String> unifyVar(String var, String x, HashMap<String, String> theta) {
		String val = theta.get(var);
		if (val != null) {
			return unify(val, x, theta);
		} 
		theta.put(var, x);
		return theta;
	}

	private static void add2KB(Node node) {
		if (node.isConnector()) {
			if (node.getValue().equals("&")) {
				add2KB(node.left);
				add2KB(node.right);
			} else {
				kb.add(getClause(node));
			}
		} else {
			kb.add(getClause(node));
		}
	}

	private static ArrayList<String> getClause(Node node) {
		ArrayList<String> literals = new ArrayList<String>();
		getLiterals(node, literals);
		return literals;
	}

	private static void getLiterals(Node node, ArrayList<String> literals) {
		if (node != null) {
			getLiterals(node.left, literals);
			if (!node.isConnector()) {
				String literal;
				if (node.isNegated()) {
					literal = "~" + node.getValue();

				} else {
					literal = node.getValue();
				}
				String[] predicate = literal.split("\\(");
				String predicateName = predicate[0];
				String[] args = predicate[1].substring(0, predicate[1].length() - 1).split(",");
				for (int i = 0; i < args.length; i++) {
					if (args[i].matches("[a-z]")) {
						args[i] = args[i] + kb.size();
					}
				}
				predicate[1] = String.join(",", args) + ")";
				literal = String.join("(", predicate);
				ArrayList<Integer> sentenceIndices = literal2SentencesMap.get(predicateName);
				if (sentenceIndices == null) {
					sentenceIndices = new ArrayList<Integer>();
				}
				literals.add(literal);
				sentenceIndices.add(kb.size());
				literal2SentencesMap.put(predicateName, sentenceIndices);
			}
			getLiterals(node.right, literals);
		}
	}

	private static void inorder(Node node) {
		if (node != null) {
			inorder(node.left);
			if (node.isNegated()) {
				System.out.print("~");
			}
			System.out.print(node.getValue());
			inorder(node.right);
		}
	}

	private static Node removeImplicationAndMoveNegationInwards(SentenceContext context) {
		if (context.predicate() != null) {
			Node node = new Node(context.predicate().getText(), false);
			return node;
		} else if (context.IMPLIES() != null) {
			Node node = new Node("|", true);
			node.left = removeImplicationAndMoveNegationInwards(context.sentence(0));
			propagateNegation(node.left);
			node.right = removeImplicationAndMoveNegationInwards(context.sentence(1));
			return node;
		} else if (context.NEG() != null) {
			Node node = removeImplicationAndMoveNegationInwards(context.sentence(0));
			propagateNegation(node);
			return node;
		} else if (context.AND() != null) {
			Node node = new Node(context.AND().getText(), true);
			node.left = removeImplicationAndMoveNegationInwards(context.sentence(0));
			node.right = removeImplicationAndMoveNegationInwards(context.sentence(1));
			return node;
		} else if (context.OR() != null) {
			Node node = new Node(context.OR().getText(), true);
			node.left = removeImplicationAndMoveNegationInwards(context.sentence(0));
			node.right = removeImplicationAndMoveNegationInwards(context.sentence(1));
			return node;
		} else {// if (context.CB() != null) {
			return removeImplicationAndMoveNegationInwards(context.sentence(0));
		}
	}

	private static void propagateNegation(Node node) {
		if (node == null)
			return;
		node.negate();
		if (node.left == null && node.right == null) {
			return;
		} else {
			propagateNegation(node.left);
			propagateNegation(node.right);
		}
	}

	private static Node distributeANDOverOR(Node node) {
		if (node.isConnector()) {
			if (node.getValue().equals("|")) {
				if (node.left.getValue().equals("&")) {
					Node n1 = new Node("|", true);
					Node n2 = new Node("|", true);
					n1.left = node.left.left;
					n1.right = node.right;
					n2.left = node.left.right;
					n2.right = node.right;
					node.setValue("&");
					node.left = distributeANDOverOR(n1);
					node.right = distributeANDOverOR(n2);
				} else if (node.right.getValue().equals("&")) {
					Node n1 = new Node("|", true);
					Node n2 = new Node("|", true);
					n1.left = node.left;
					n1.right = node.right.left;
					n2.left = node.left;
					n2.right = node.right.right;
					node.setValue("&");
					node.left = distributeANDOverOR(n1);
					node.right = distributeANDOverOR(n2);
				}
			}
		}
		return node;
	}

}

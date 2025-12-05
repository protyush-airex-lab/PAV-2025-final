// This file has the helper functions needed for output formatting and printing the CFG

package pav;

import java.util.Arrays;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.NormalUnitPrinter;
import soot.SootMethod;
import soot.Unit;
import soot.UnitPrinter;
import soot.jimple.Stmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.cfgcmd.CFGToDotGraph;
import soot.util.dot.DotGraph;

public class Base {
	public static class ResultTuple {
		public final String m;
		public final String p;
		public final String v;
		public final List<String> pV;
		
		public ResultTuple(String method, String prgpoint, String varname, List<String> pointerValues) {
			this.m = method;
			this.p = prgpoint;
			this.v = varname;
			this.pV = pointerValues;
		}
	}

	// Logger for logging messages
	public class SLF4J {
		public static Logger LOGGER = LoggerFactory.getLogger(SLF4J.class);
	}

	// Protected functions for formatting output
	protected static String getProgramPointName(int st1) {
		String name1 = "in" + String.format("%02d", st1);
		return name1;
	}

	protected static String formatOutputLine(ResultTuple tup, String prefix) {
		String line = tup.m + ": " + tup.p + ": " + tup.v + ": " + "{";
		List<String> pointerValues = tup.pV;
		for(String pointers: pointerValues) {
			line += pointers+", ";
		}
		line= line+"}";
		return (prefix + line);
	}

	protected static String fmtOutputLine(ResultTuple tup) {
		return formatOutputLine(tup, "");
	}

	protected static String[] formatOutputData(Set<ResultTuple> data, String prefix) {

		String[] outputlines = new String[ data.size() ];

		int i = 0;
		for (ResultTuple tup : data) {
			outputlines[i] = formatOutputLine(tup, prefix);
			i++;
		}

		Arrays.sort(outputlines);
		return outputlines;
	}

	protected static String[] formatOutputData(Set<ResultTuple> data) {
		return formatOutputData(data, "");
	}

	// Returns true if 'dot' exists in PATH and runs successfully
	private static boolean isGraphvizInstalled() {
		try {
			Process process = new ProcessBuilder("dot", "-V").redirectErrorStream(true).start();
			process.waitFor();
			return process.exitValue() == 0;
		} catch (Exception e) {
				return false;
		}
	}

	// Generates PNG from dot file using Graphviz 'dot' command
	private static boolean generatePngFromDot(String dotPath, String pngPath) {
		try {
			Process process = new ProcessBuilder("dot", "-Tpng", dotPath, "-o", pngPath)
				.redirectErrorStream(true).start();
			process.waitFor();
			return process.exitValue() == 0;
		} catch (Exception e) {
			return false;
		}
	}

	// Public functions for printing CFG and method info
	public static void drawMethodDependenceGraph(SootMethod method) {
		String outputDirectory = "output/";
		if (!method.isPhantom() && method.isConcrete()) {
			Body body = method.retrieveActiveBody();
			ExceptionalUnitGraph graph = new ExceptionalUnitGraph(body);

			// Output the CFG to a dot file
			String dotFile = outputDirectory + method.getName() + ".dot";
			CFGToDotGraph cfgForMethod = new CFGToDotGraph();
			cfgForMethod.drawCFG(graph);
			DotGraph cfgDot =  cfgForMethod.drawCFG(graph);
			cfgDot.plot(dotFile);

			// Create PNG from these dotfiles if Graphviz is installed
			if(isGraphvizInstalled()) {
				String pngFile = outputDirectory + method.getName() + ".png";
				boolean success = generatePngFromDot(dotFile, pngFile);
				if (!success) {
				    System.out.println("Failed to create PNG from DOT");
				}
			} else {
			    System.out.println("Graphviz is not installed or not in PATH");
			}
		}
	}

	public static void printUnit(int lineno, Body b, Unit u) {
		UnitPrinter up = new NormalUnitPrinter(b);
		u.toString(up);
		String linenostr = String.format("%02d", lineno) + ": ";
		System.out.println(linenostr + up.toString());
	}

	public static void printInfo(SootMethod entryMethod) {
		if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
			Body body = entryMethod.retrieveActiveBody();
	
			int lineno = 0;
			for (Unit u : body.getUnits()) {
				if (!(u instanceof Stmt)) {
					continue;
				}
				printUnit(lineno, body, u);
				lineno++;
			}
		}
	}
}
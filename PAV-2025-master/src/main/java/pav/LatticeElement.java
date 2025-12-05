package pav;

// Put your LatticeElement interface definition in this file

import soot.jimple.Stmt;

/* Receiver object of LatticeElement possess the existing dataflow fact at a program point.
 * x.join_op(y) -> here x, y are elements of type, LatticeElement and x is the receiver object.
 * Method implementation should not modify the receiver object. A fresh object should be returned.
 * Killdall's algorithm should access the dataflow facts only as type LatticeElement and should work on any implementation of LatticElement for any analysis.
 */

interface LatticeElement {
	public LatticeElement join_op(LatticeElement r);
	/* represents: "this" JOIN "r"
	 * this - the existing dataflow fact
	 * r    - the incoming dataflow fact
	 */

	public boolean equals(LatticeElement r);

	public LatticeElement tf_assign(Stmt st);

	public LatticeElement tf_cond(boolean b, Stmt st);
}
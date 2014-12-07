// Copyright (c) 2012, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//    * Redistributions of source code must retain the above copyright
//      notice, this list of conditions and the following disclaimer.
//    * Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimer in the
//      documentation and/or other materials provided with the distribution.
//    * Neither the name of the <organization> nor the
//      names of its contributors may be used to endorse or promote products
//      derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL DAVID J. PEARCE BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

package wyil.builders;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import wycc.lang.SyntaxError;
import wycc.lang.SyntaxError.*;
import wycc.util.Pair;
import wycs.core.Value;
import wycs.solver.Solver;
import wycs.syntax.Expr;
import static wycs.solver.Solver.*;
import wyautl.core.Automaton;
import wyautl.io.PrettyAutomataWriter;
import static wyil.util.ErrorMessages.internalFailure;
import wyil.lang.*;
import wyil.util.AttributedCodeBlock;

/**
 * <p>
 * Represents a path through the body of a Wyil method or function. A branch
 * accumulates the constraints known to hold through that particular execution
 * path. These constraints can then be checked for satisfiability at various
 * critical points in the function.
 * </p>
 * <p>
 * When verifying a given function or method, the verifier starts with a single
 * branch at the beginning of the method. When split points in the control-flow
 * graph are encountered, branches are accordingly forked off to represent the
 * alternate control-flow path. At control-flow meet points, branches may also
 * be joined back together (although this is not always strictly necessary). A
 * diagrammatic view might be:
 * </p>
 *
 * <pre>
 *  entry
 *   ||
 *   ||
 *   ##\
 *   ||\\
 *   || \\
 *   || ||
 *   || ##\
 *   || ||\\
 *   ||//  \\
 *   ##/   ||
 *   ||    ||
 *   \/    \/
 *   B1    B3
 * </pre>
 * <p>
 * In the above example, we initially start with one branch <code>B1</code>.
 * This is then forked to give branch <code>B2</code> which, in turn, is forked
 * again to give <code>B3</code>. Subsequently, branch <code>B2</code> is joined
 * back with <code>B1</code>. However, <code>B3</code> is never joined and
 * terminates separately.
 * </p>
 * <p>
 * Every branch (except the first) has a <i>parent</i> branch which it was
 * forked from. Given any two branches there is always a <i>Least Common
 * Ancestor (LCA)</i> --- that is, the latest point which is common to both
 * branches. Finding the LCA can be useful, for example, to identify constraints
 * common to both branches.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class VcBranch {
	/**
	 * The parent branch which this branch was forked from, or <code>null</code>
	 * if it is the initial "master" branch for the function or method in
	 * question.
	 */
	private final VcBranch parent;

	/**
	 * Maintains the current assignment of variables to expressions.
	 */
	private final Expr[] environment;

	/**
	 * Maintains the current assignment of variables to their types.
	 */
	private final Type[] types;

	/**
	 * The root block of Wyil bytecode instructions which this branch is
	 * traversing (note: <code>parent == null || block == parent.block</code>
	 * must hold).
	 */
	private final AttributedCodeBlock block;

	/**
	 * The bytecode index into the above block that this branch is currently at.
	 */
	private CodeBlock.Index pc;

	/**
	 * Construct the master verification branch for a given attributed code
	 * block. The pc for the master branch of a block is the root index (i.e.
	 * the branch begins at the entry of the block).
	 *
	 * @param block
	 *            --- the block of code on which this branch is operating.
	 * @param numInputs
	 *            --- the number of inputs to the given block.
	 */
	public VcBranch(AttributedCodeBlock block, int numInputs) {
		int numSlots = Math.max(numInputs,block.numSlots());
		this.parent = null;
		this.block = block;
		this.environment = new Expr[numSlots];
		this.types = new Type[numSlots];
		this.pc = CodeBlock.Index.ROOT;
	}

	/**
	 * Construct the master verification branch for a given code block. The pc
	 * for the master branch of a block is the root index (i.e. the branch
	 * begins at the entry of the block).
	 *
	 * @param decl
	 *            --- the enclosing declaration.
	 * @param block
	 *            --- the block of code on which this branch is operating.
	 */
	public VcBranch(WyilFile.FunctionOrMethodDeclaration decl, AttributedCodeBlock block) {
		ArrayList<Type> paramTypes = decl.type().params();
		int numSlots = Math.max(paramTypes.size(),block.numSlots());
		this.parent = null;
		this.environment = new Expr[numSlots];
		this.types = new Type[numSlots];
		this.block = block;
		this.pc = CodeBlock.Index.ROOT;
	}

	/**
	 * Private constructor used for forking a child-branch from a parent branch.
	 *
	 * @param parent
	 *            --- parent branch being forked from.
	 */
	private VcBranch(VcBranch parent) {
		this.parent = parent;
		this.environment = parent.environment.clone();
		this.types = Arrays
				.copyOf(parent.types, environment.length);
		this.block = parent.block;
		this.pc = parent.pc;		
	}

	/**
	 * Return the current Program Counter (PC) value for this branch. This must
	 * be a valid index into the code block this branch is operating over.
	 *
	 * @return
	 */
	public CodeBlock.Index pc() {
		return pc;
	}
	
	/**
	 * Get the constraint variable which corresponds to the given Wyil bytecode
	 * register at this point on this branch.
	 *
	 * @param register
	 * @return
	 */
	public Expr read(int register) {
		return environment[register];
	}

	/**
	 * Get the type of a given register at this point in the block.
	 *
	 * @return
	 */
	public Type typeOf(String var) {		
		// FIXME: this is such an *horrific* hack, I can't believe I'm doing it.
		// But, it does work most of the time :(
		String[] split = var.split("_");
		int register = Integer.parseInt(split[0].substring(1));
		return types[register];
	}

	/**
	 * Get the type of a given register at this point in the block.
	 *
	 * @return
	 */
	public Type typeOf(int register) {
		return types[register];
	}

	/**
	 * Assign an expression to a given Wyil bytecode register. This stores the
	 * assigned expression for recall when the given register is subsequently
	 * read.
	 *
	 * @param register
	 *            --- Register being written.
	 * @param expr
	 *            --- Expression being assigned.
	 * @param type
	 *            --- Type of expression being assigned.
	 */
	public void write(int register, Expr expr, Type type) {
		environment[register] = expr;
		types[register] = type;
	}

	/**
	 * Terminate the current flow for a given register and begin a new one. In
	 * terms of static-single assignment, this means simply change the index of
	 * the register in question. This is also known in the verification
	 * community as "havocing" the variable, or sending the variable to "havoc".
	 *
	 * @param register
	 *            Register number to invalidate
	 * @param type
	 *            Type of register being invalidated
	 */
	public Expr.Variable invalidate(int register, Type type) {
		// to invalidate a variable, we assign it a "skolem" constant. That is,
		// a fresh variable which has not been previously encountered in the
		// branch.				
		Expr.Variable var = new Expr.Variable("r" + Integer.toString(register) + "_" + pc);
		environment[register] = var;
		types[register] = type;
		return var;
	}

	/**
	 * Invalidate all registers from <code>start</code> upto (but not including)
	 * <code>end</code>.
	 *
	 * @param start
	 *            --- first register to invalidate.
	 * @param end
	 *            --- first register not to invalidate.
	 */
	public void invalidate(int start, int end, Type type) {
		for (int i = start; i != end; ++i) {
			invalidate(i,type);
		}
	}

	/**
	 * Assume a given condition holds on this branch.
	 * 
	 * @param e
	 *            The condition to assume
	 */
	public void assume(Expr e) {
		
	}
	
	/**
	 * <p>
	 * Fork a child-branch from this branch. The child branch is (initially)
	 * identical in every way to the parent, however the expectation is that
	 * they will diverge.
	 * </p>
	 *
	 * <pre>
	 *    B1
	 *    ||
	 *    ||
	 *    ##    <- origin
	 *    | \
	 *    ||\\
	 *    || \\
	 *    \/  \/
	 *    B1  B2
	 * </pre>
	 * <p>
	 * The origin for the forked branch is the <code>PC</code value at the split
	 * point. Initially, the <code>PC</code> value for the forked branch is
	 * identical to that of the parent, however it is expected that a
	 * <code>goTo</code> will be used immediately after the fork to jump the
	 * child branch to its logical starting point.
	 * </p>
	 * <p>
	 * A new environment is created for the child branch which, initially, is
	 * identical to that of the parent. As assignments to variables are made on
	 * either branch, these environments will move apart.
	 * </p>
	 *
	 * @return --- The child branch which is forked off this branch.
	 */
	public VcBranch fork() {
		return new VcBranch(this);
	}

	/**
	 * <p>
	 * Merge descendant (i.e. a child or child-of-child, etc) branch back into
	 * this branch. The constraints for this branch must now correctly capture
	 * those constraints that hold coming from either branch (i.e. this
	 * represents a meet-point in the control-flow graph).
	 * </p>
	 * <p>
	 * To generate the constraints which hold after the meet, we take the
	 * logical OR of those constraints holding on this branch prior to the meet
	 * and those which hold on the incoming branch. For example, support we
	 * have:
	 * </p>
	 *
	 * <pre>
	 * 	 y$0 != 0    y$0 != 0
	 *   && x$1 < 1  && x$2 >= 1
	 *        ||      ||
	 *         \\    //
	 *          \\  //
	 *           \\//
	 *            ##
	 *   y$0 != 0 &&
	 * ((x$1 < 1 && x$3 == x$1) ||
	 *  (x$2 >= 1 && x$3 == x$2))
	 * </pre>
	 * <p>
	 * Here, we see that <code>y$0 != 0</code> is constant to both branches and
	 * is ommitted from the disjunction. Furthermore, we've added an assignment
	 * <code>x$3 == </code> onto both sides of the disjunction to capture the
	 * flow of variable <code>x</code> from both sides (since it was modified on
	 * at least one of the branches).
	 * </p>
	 * <p>
	 * One challenge is to determine constraints which are constant to both
	 * sides. Eliminating such constraints from the disjunction reduces the
	 * overall work of the constraint solver.
	 * </p>
	 *
	 * @param incoming
	 *            --- The descendant branch which is being merged into this one.
	 */
	private void join(VcBranch incoming) {
		// First, determine new constraint sequence
		ArrayList<Expr> common = new ArrayList<Expr>();
		ArrayList<Expr> lhsConstraints = new ArrayList<Expr>();
		ArrayList<Expr> rhsConstraints = new ArrayList<Expr>();

		splitConstraints(incoming,common,lhsConstraints,rhsConstraints);

		// Finally, put it all together
		Expr l = And(lhsConstraints);
		Expr r = And(rhsConstraints);

		// can now compute the logical OR of both branches
		Expr join = Or(l,r);

		// now, clear our sequential constraints since we can only have one
		// which holds now: namely, the or of the two branches.
		Scope top = topScope();
		top.constraints.clear();
		top.constraints.addAll(common);
		top.constraints.add(join);
	}

	/**
	 * Split the constraints for this branch and the incoming branch into three
	 * sets: those common to both; those unique to this branch; and, those
	 * unique to the incoming branch.
	 *
	 * @param incoming
	 * @param common
	 * @param myRemainder
	 * @param incomingRemainder
	 */
	private void splitConstraints(VcBranch incoming, ArrayList<Expr> common,
			ArrayList<Expr> myRemainder, ArrayList<Expr> incomingRemainder) {
		ArrayList<Expr> constraints = topScope().constraints;
		ArrayList<Expr> incomingConstraints = incoming.topScope().constraints;

		int min = 0;

		while (min < constraints.size() && min < incomingConstraints.size()) {
			Expr is = constraints.get(min);
			Expr js = incomingConstraints.get(min);
			if (is != js) {
				break;
			}
			min = min + 1;
		}

		for(int k=0;k<min;++k) {
			common.add(constraints.get(k));
		}
		for(int i = min;i < constraints.size();++i) {
			myRemainder.add(constraints.get(i));
		}
		for(int j = min;j < incomingConstraints.size();++j) {
			incomingRemainder.add(incomingConstraints.get(j));
		}
	}

	public Expr And(List<Expr> constraints) {
		if(constraints.size() == 0) {
			return new Expr.Constant(Value.Bool(true));
		} else if(constraints.size() == 1) {
			return constraints.get(0);
		} else {
			Expr nconstraints = null;
			for (Expr e : constraints) {
				if(nconstraints == null) {
					nconstraints = e;
				} else {
					nconstraints = new Expr.Binary(Expr.Binary.Op.AND,e,nconstraints,e.attributes());
				}
			}
			return nconstraints;
		}
	}

	public Expr Or(Expr... constraints) {
		if (constraints.length == 0) {
			return new Expr.Constant(Value.Bool(false));
		} else if (constraints.length == 1) {
			return constraints[0];
		} else {
			Expr nconstraints = null;
			for (Expr e : constraints) {
				if (nconstraints == null) {
					nconstraints = e;
				} else {
					nconstraints = new Expr.Binary(Expr.Binary.Op.OR, e,
							nconstraints, e.attributes());
				}
			}
			return nconstraints;
		}
	}
}

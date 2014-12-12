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

import wycc.lang.SyntaxError.InternalFailure;
import wycc.lang.SyntaxError;
import static wyil.util.ErrorMessages.*;

import java.math.BigInteger;
import java.util.*;

import wyautl.util.BigRational;
import wybs.lang.*;
import wyfs.lang.Path;
import wyil.lang.*;
import wyil.util.AttributedCodeBlock;
import wyil.util.ErrorMessages;
import wycc.lang.Attribute;
import wycc.lang.NameID;
import wycc.lang.SyntacticElement;
import wycc.util.Pair;
import wycs.core.SemanticType;
import wycs.core.Value;
import wycs.syntax.*;

/**
 * Responsible for converting a given Wyil bytecode into an appropriate
 * constraint which encodes its semantics.
 *
 * @author David J. Pearce
 *
 */
public class VcGenerator {
	private final Builder builder;
	private final WyalFile wycsFile;
	private final String filename;
	
	/**
	 * The root block of Wyil bytecode instructions which this branch is
	 * traversing (note: <code>parent == null || block == parent.block</code>
	 * must hold).
	 */
	private AttributedCodeBlock rootBlock;


	public VcGenerator(Builder builder, WyalFile wycsFile,
			String filename) {
		this.builder = builder;
		this.filename = filename;
		this.wycsFile = wycsFile;
	}

	public String filename() {
		return filename;
	}

	private static int indexCount = 0;

	// ===============================================================================
	// Block controller
	// ===============================================================================
	
	/**
	 * <p>
	 * Transform a given vc branch over a block of zero or more statements. In
	 * the case of a straight-line sequence, this is guaranteed to produce at
	 * most one outgoing branch (zero is possible if sequence includes a
	 * return). For an instruction sequence with one or more conditional
	 * branches, multiple branches may be produced representing the different
	 * possible traversals.
	 * </p>
	 * <p>
	 * This function symbolically executes each branch it is maintaining until
	 * it either terminates (e.g. returns), or leaves the block.
	 * </p>
	 * 
	 * @param index
	 *            The index in the root block of the given block.
	 * @param block
	 *            The block being transformed over.
	 * @param entryState
	 *            the initial state on entry to the block. This is assumed to be
	 *            located at the first instruction of the block.
	 * 
	 */
	protected List<VcBranch> transform(CodeBlock.Index parent, CodeBlock block, VcBranch entryState) {
		ArrayList<VcBranch> branches = new ArrayList<VcBranch>();
		branches.add(entryState);
		
		for(int i=0;i!=branches.size();++i) {
			VcBranch branch = branches.get(i);
			
			// The program counter represents the current position of the branch
			// being explored. 
			CodeBlock.Index pc = branch.pc();
			
			// Execute this branch provided it is still within the parent block.
			// If it is outside of this block, then that means it has branched
			// to an enclosing block. 			
			while(pc.isWithin(parent)) {
				
				// FIXME: there is a bug here when a bytecode goes over the end
				// of the block. 
				
				Code code = block.get(branch.pc());
				// Now, dispatch statements. Control statements are treated
				// specially from unit statements.
				if (code instanceof Codes.Goto) {
					transform((Codes.Goto) code,i,branches);
				} else if (code instanceof Codes.If) {
					transform((Codes.If) code,i,branches);
				} else if (code instanceof Codes.IfIs) {
					transform((Codes.IfIs) code,i,branches);
				} else if (code instanceof Codes.Switch) {
					transform((Codes.Switch) code,i,branches);
				} else if (code instanceof Codes.ForAll) {
					transform((Codes.ForAll) code,i,branches);
				} else if (code instanceof Codes.Loop) {
					transform((Codes.Loop) code,i,branches);
				} else if (code instanceof Codes.Return) {
					transform((Codes.Return) code,i,branches);
				} else if (code instanceof Codes.Fail) {
					transform((Codes.Fail) code,i,branches);
				} else {
					// Unit statement
					transform(code,branch);
					gotoNext(branch);
				}
			}
		}
		
		return branches;
	}
	
	// ===============================================================================
	// Control Bytecodes
	// ===============================================================================
	

	/**
	 * <p>
	 * Transform a branch through a loop bytecode. This is done by splitting the
	 * entry branch into the case for the loop body, and the case for the loop
	 * after. First, modified variables are invalidated to disconnect them from
	 * information which held before the loop. Second, the loop invariant is
	 * assumed as this provides the only information known about modified
	 * variables.
	 * </p>
	 * 
	 * <p>
	 * For the case of the loop body, there are several scenarios. For branches
	 * which make it to the end of the body, the loop invariant must be
	 * reestablished. For branches which exit the loop, these are then folded
	 * into enclosing scope.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.Loop code, int branchIndex, List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		
		// First, havoc all variables which are modified in the loop.
		for (int i : code.modifiedOperands) {
			branch.invalidate(i,branch.typeOf(i));
		}

	}

	/**
	 * <p>
	 * Transform a branch through a loop bytecode. This is done by splitting the
	 * entry branch into the case for the loop body, and the case for the loop
	 * after. First, modified variables are invalidated to disconnect them from
	 * information which held before the loop. Second, the loop invariant is
	 * assumed as this provides the only information known about modified
	 * variables.
	 * </p>
	 * 
	 * <p>
	 * For the case of the loop body, there are several scenarios. For branches
	 * which make it to the end of the body, the loop invariant must be
	 * reestablished. For branches which exit the loop, these are then folded
	 * into enclosing scope.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.ForAll code, int branchIndex, List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		
		// First, havoc all variables which are modified in the loop.
		for (int i : code.modifiedOperands) {
			branch.invalidate(i,branch.typeOf(i));
		}

		Expr.Variable var = branch.invalidate(code.indexOperand,code.type.element());


	}
	
	/**
	 * <p>
	 * Transform a branch through a conditional bytecode. This is done by
	 * splitting the entry branch into the case for the true branch and the case
	 * for the false branch. Control then continues down each branch.
	 * </p>
	 * <p>
	 * On the true branch, the condition is assumed to hold. In contrast, the
	 * condition's inverse is assumed to hold on the false branch.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.If code, int branchIndex, List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		// First, clone and register the branch
		VcBranch trueBranch = branch.fork();
		branches.add(trueBranch);		
		// Second assume the condition on each branch
		Expr.Binary trueTest = buildTest(code.op, code.leftOperand,
				code.rightOperand, code.type, trueBranch);
		trueBranch.assume(trueTest);
		branch.assume(invert(trueTest));
		// Finally dispacth the branches
		gotoNext(branch);
		gotoLabel(code.target,branch);
	}

	/**
	 * <p>
	 * Transform a branch through a conditional bytecode. This is done by
	 * splitting the entry branch into the case for the true branch and the case
	 * for the false branch. Control then continues down each branch.
	 * </p>
	 * <p>
	 * On the true branch, the condition is assumed to hold. In contrast, the
	 * condition's inverse is assumed to hold on the false branch.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.IfIs code, int branchIndex, List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		Type type = branch.typeOf(code.operand);
		// First, determine the true test
		Type trueType = Type.intersect(type,code.rightOperand);
		Type falseType = Type.intersect(type,Type.Negation(code.rightOperand));

		if(trueType.equals(Type.T_VOID)) {
			// This indicate that the true branch is unreachable and
			// should not be explored. Observe that this does not mean
			// the true branch is dead-code. Rather, since we're
			// preforming a path-sensitive traversal it means we've
			// uncovered an unreachable path. In this case, this branch
			// remains as the false branch.
			branch.write(code.operand, branch.read(code.operand), falseType);
		} else if(falseType.equals(Type.T_VOID)) {
			// This indicate that the false branch is unreachable (ditto
			// as for true branch). In this case, this branch becomes
			// the true branch.
			branch.write(code.operand, branch.read(code.operand), trueType);
			gotoLabel(code.target,branch);
		} else {
			// In this case, both branches are reachable.
			// First, clone and register the branch
			VcBranch trueBranch = branch.fork();
			branches.add(trueBranch);		
			// Second retype variables on each branch
			branch.write(code.operand, branch.read(code.operand), falseType);
			trueBranch.write(code.operand, branch.read(code.operand), trueType);
			// Finally dispatch the branches
			gotoNext(branch);
			gotoLabel(code.target,branch);
		}
	}
	
	/**
	 * <p>
	 * Transform a branch through a switch bytecode. This is done by splitting
	 * the entry branch into separate branches for each case. The entry branch
	 * then follows the default branch.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.Switch code, int branchIndex,
			List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		// First, for each case fork a new branch to traverse it.
		VcBranch[] cases = new VcBranch[code.branches.size()];
		for (int i = 0; i != cases.length; ++i) {
			cases[i] = branch.fork();
			branches.add(cases[i]);
		}

		// Second, for each case, assume that the variable switched on matches
		// the give case value. Likewise, assume that the default branch does
		// *not* equal this value.
		for (int i = 0; i != cases.length; ++i) {
			Constant caseValue = code.branches.get(i).first();
			// Second, on the new branch we need assume that the variable being
			// switched on matches the given value.
			Expr src = branch.read(code.operand);
			Expr constant = new Expr.Constant(convert(caseValue, branch),
					wycsAttributes(branch));
			cases[i].assume(new Expr.Binary(Expr.Binary.Op.EQ, src, constant,
					wycsAttributes(branch)));
			// Third, on the default branch we can assume that the variable
			// being switched is *not* the given value.
			branch.assume(new Expr.Binary(Expr.Binary.Op.NEQ, src, constant,
					wycsAttributes(branch)));
		}

		// Finally, the original entry branch now represents the default branch.
		// Therefore, dispatch this to the default target.
		gotoLabel(code.defaultTarget, branch);
	}
	
	/**
	 * <p>
	 * Transform a branch through an unconditional branching bytecode. This is
	 * pretty straightforward, and the branch is just directed to the given
	 * location.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.Goto code, int branchIndex, List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		gotoLabel(code.target,branch);
	}

	/**
	 * <p>
	 * Transform a branch through the special fail bytecode.  In the normal case,
	 * we must establish this branch is unreachable. However, in the case that
	 * we are within an enclosing assume statement, then we can simply discard
	 * this branch.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.Fail code, int branchIndex, List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		// FIXME: 
//		VcBranch.AssertOrAssumeScope scope = branch.topScope(VcBranch.AssertOrAssumeScope.class);
//
//		if (scope.isAssertion) {
//			Expr assumptions = branch.constraints();
//			Expr implication = new Expr.Binary(Expr.Binary.Op.IMPLIES,
//					assumptions, new Expr.Constant(Value.Bool(false),
//							attributes(branch)));
//			// build up list of used variables
//			HashSet<String> uses = new HashSet<String>();
//			implication.freeVariables(uses);
//			// Now, parameterise the assertion appropriately
//			Expr assertion = buildAssertion(0, implication, uses, branch);
//			wycsFile.add(wycsFile.new Assert(code.message.value, assertion,
//					attributes(branch)));
//		} else {
//			// do nothing?
//		}
	}

	/**
	 * <p>
	 * Transform a branch through a return bytecode. In this case, we need to
	 * ensure that the postcondition holds. After that, we can drop the branch
	 * since it is completed.
	 * </p>
	 * 
	 * @param code
	 *            The bytecode being transformed.
	 * @param branchIndex
	 *            The index of the branch (in branches) which holds on entry to
	 *            the bytecode.
	 * @param branches
	 *            The list of branches currently being managed.
	 */
	protected void transform(Codes.Return code, int branchIndex, List<VcBranch> branches) {
		VcBranch branch = branches.get(branchIndex);
		// FIXME
		branches.set(branchIndex,null); // kill the branch!
	}


	// ===============================================================================
	// Unit Bytecodes
	// ===============================================================================
	
	/**
	 * Dispatch transform over unit bytecodes. Each unit bytecode is guaranteed
	 * to continue afterwards, and not to fork any new branches.
	 * 
	 * @param code The bytecode being transformed over.
	 * @param branch The branch on entry to the bytecode.
	 */
	protected void transform(Code code, VcBranch branch) {
		try {
			if (code instanceof Codes.LengthOf) {
				transformUnary(Expr.Unary.Op.LENGTHOF,(Codes.LengthOf) code,branch);
			} else if (code instanceof Codes.BinaryOperator) {
				Codes.BinaryOperator bc = (Codes.BinaryOperator) code;
				transformBinary(binaryOperatorMap[bc.kind.ordinal()], bc, branch);
			} else if (code instanceof Codes.ListOperator) {
				Codes.ListOperator bc = (Codes.ListOperator) code;
				transformBinary(Expr.Binary.Op.LISTAPPEND, bc, branch);
			} else if (code instanceof Codes.SetOperator) {
				Codes.SetOperator bc = (Codes.SetOperator) code;
				transformBinary(setOperatorMap[bc.kind.ordinal()], bc, branch);
			} else if (code instanceof Codes.NewList) {
				transformNary(Expr.Nary.Op.LIST,(Codes.NewList) code,branch);
			} else if (code instanceof Codes.NewRecord) {
				transformNary(Expr.Nary.Op.TUPLE,(Codes.NewTuple) code,branch);
			} else if (code instanceof Codes.NewSet) {
				transformNary(Expr.Nary.Op.SET,(Codes.NewSet) code,branch);
			} else if (code instanceof Codes.NewTuple) {
				transformNary(Expr.Nary.Op.TUPLE,(Codes.NewTuple) code,branch);
			} else if (code instanceof Codes.Convert) {
				transform((Codes.Convert) code, branch);
			} else if (code instanceof Codes.Const) {
				transform((Codes.Const) code, branch);
			} else if (code instanceof Codes.Debug) {
				// skip
			} else if (code instanceof Codes.FieldLoad) {
				transform((Codes.FieldLoad) code, branch);
			} else if (code instanceof Codes.IndirectInvoke) {
				transform((Codes.IndirectInvoke) code, branch);
			} else if (code instanceof Codes.Invoke) {
				transform((Codes.Invoke) code, branch);
			} else if (code instanceof Codes.Invert) {
				transform((Codes.Invert) code, branch);
			} else if (code instanceof Codes.Label) {
				// skip
			} else if (code instanceof Codes.SubList) {
				transform((Codes.SubList) code, branch);
			} else if (code instanceof Codes.IndexOf) {
				transform((Codes.IndexOf) code, branch);
			} else if (code instanceof Codes.Move) {
				transform((Codes.Move) code, branch);
			} else if (code instanceof Codes.Assign) {
				transform((Codes.Assign) code, branch);
			} else if (code instanceof Codes.Update) {
				transform((Codes.Update) code, branch);
			} else if (code instanceof Codes.NewMap) {
				transform((Codes.NewMap) code, branch);
			}  else if (code instanceof Codes.UnaryOperator) {
				transform((Codes.UnaryOperator) code, branch);
			} else if (code instanceof Codes.Dereference) {
				transform((Codes.Dereference) code, branch);
			} else if (code instanceof Codes.Nop) {
				// skip
			} else if (code instanceof Codes.StringOperator) {
				transform((Codes.StringOperator) code, branch);
			} else if (code instanceof Codes.SubString) {
				transform((Codes.SubString) code, branch);
			} else if (code instanceof Codes.NewObject) {
				transform((Codes.NewObject) code, branch);
			} else if (code instanceof Codes.TupleLoad) {
				transform((Codes.TupleLoad) code, branch);
			} else {
				internalFailure("unknown: " + code.getClass().getName(),
						filename(), rootBlock.attributes(branch.pc()));
			}
		} catch (InternalFailure e) {
			throw e;
		} catch (SyntaxError e) {
			throw e;
		} catch (Throwable e) {
			internalFailure(e.getMessage(), filename(), e, rootBlock.attributes(branch.pc()));
		}				
	}
	
	protected void transform(Codes.Assign code, VcBranch branch) {
		branch.write(code.target(), branch.read(code.operand(0)), code.assignedType());
	}

	/**
	 * Maps binary bytecodes into expression opcodes.
	 */
	private static Expr.Binary.Op[] binaryOperatorMap = {
		Expr.Binary.Op.ADD,
		Expr.Binary.Op.SUB,
		Expr.Binary.Op.MUL,
		Expr.Binary.Op.DIV,
		Expr.Binary.Op.RANGE
	};

		/**
	 * Maps binary bytecodes into expression opcodes.
	 */
	private static Expr.Binary.Op[] setOperatorMap = {
		Expr.Binary.Op.SETUNION,
		Expr.Binary.Op.SETINTERSECTION,
		Expr.Binary.Op.SETDIFFERENCE
	};
	
	protected void transform(Codes.StringOperator code, VcBranch branch) {
		Collection<Attribute> attributes = wycsAttributes(branch);
		Expr lhs = branch.read(code.operand(0));
		Expr rhs = branch.read(code.operand(1));

		switch (code.kind) {
		case APPEND:
			// do nothing
			break;
		case LEFT_APPEND:
			rhs = new Expr.Nary(Expr.Nary.Op.LIST,new Expr[] { rhs }, attributes);
			break;
		case RIGHT_APPEND:
			lhs = new Expr.Nary(Expr.Nary.Op.LIST,new Expr[] { lhs }, attributes);
			break;
		default:
			internalFailure("unknown binary operator", filename,
					rootBlock.attributes(branch.pc()));
			return;
		}

		// TODO: after removing left append we can simplify this case.
		
		branch.write(code.target(), new Expr.Binary(Expr.Binary.Op.LISTAPPEND,
				lhs, rhs, wycsAttributes(branch)), code.assignedType());
	}

	protected void transform(Codes.Convert code, VcBranch branch) {
		Expr result = branch.read(code.operand(0));
		// TODO: actually implement some or all coercions?
		branch.write(code.target(), result, code.assignedType());
	}

	protected void transform(Codes.Const code, VcBranch branch) {
		Value val = convert(code.constant, branch);
		branch.write(code.target(), new Expr.Constant(val, wycsAttributes(branch)),
				code.assignedType());
	}

	protected void transform(Codes.Debug code, VcBranch branch) {
		// do nout
	}

	protected void transform(Codes.Dereference code, VcBranch branch) {
		// TODO
		branch.invalidate(code.target(),code.type());
	}

	protected void transform(Codes.FieldLoad code, VcBranch branch) {
		ArrayList<String> fields = new ArrayList<String>(code.type().fields()
				.keySet());
		Collections.sort(fields);
		Expr src = branch.read(code.operand(0));
		Expr index = new Expr.Constant(Value.Integer(BigInteger.valueOf(fields
				.indexOf(code.field))));
		Expr result = new Expr.IndexOf(src, index, wycsAttributes(branch));
		branch.write(code.target(), result, code.assignedType());
	}

	protected void transform(Codes.IndirectInvoke code, VcBranch branch) {
		// TODO
		if(code.target() != Codes.NULL_REG) {
			branch.invalidate(code.target(),code.type().ret());
		}
	}

	protected void transform(Codes.Invoke code, VcBranch branch)
			throws Exception {
		Collection<Attribute> attributes = wycsAttributes(branch);
		int[] code_operands = code.operands();
		if (code.target() != Codes.NULL_REG) {
			// Need to assume the post-condition holds.
			Expr[] operands = new Expr[code_operands.length];
			for (int i = 0; i != code_operands.length; ++i) {
				operands[i] = branch.read(code_operands[i]);
			}
			Expr argument = new Expr.Nary(Expr.Nary.Op.TUPLE, operands,
					attributes);
			branch.write(code.target(), new Expr.Invoke(
					toIdentifier(code.name), code.name.module(),
					Collections.EMPTY_LIST, argument, attributes), code
					.assignedType());

			// Here, we must add a WycsFile Function to represent the function being called, and to prototype it.
			TypePattern from = new TypePattern.Leaf(convert(code.type()
					.params(), branch), null, attributes);
			TypePattern to = new TypePattern.Leaf(convert(code.type().ret(),
					branch), null, attributes);
			wycsFile.add(wycsFile.new Function(toIdentifier(code.name),
					Collections.EMPTY_LIST, from, to, null));

			List<AttributedCodeBlock> ensures = findPostcondition(code.name, code.type(),
					branch);

			if (ensures.size() > 0) {
				// operands = Arrays.copyOf(operands, operands.length);
				Expr[] arguments = new Expr[operands.length + 1];
				System.arraycopy(operands, 0, arguments, 1, operands.length);
				arguments[0] = branch.read(code.target());
				ArrayList<Type> paramTypes = code.type().params();
				Type[] types = new Type[paramTypes.size()+1];
				for(int i=0;i!=paramTypes.size();++i) {
					types[i+1] = paramTypes.get(i);
				}
				types[0] = branch.typeOf(code.target());
				for (AttributedCodeBlock postcondition : ensures) {
					Expr constraint = transformExternalBlock(postcondition,
							arguments, types, branch);
					// assume the post condition holds
					branch.assume(constraint);
				}
			}
		}
	}

	protected void transform(Codes.Invert code, VcBranch branch) {
		// TODO
		branch.invalidate(code.target(),code.type());
	}

	protected void transform(Codes.IndexOf code, VcBranch branch) {
		Expr src = branch.read(code.operand(0));
		Expr idx = branch.read(code.operand(1));
		branch.write(code.target(), new Expr.IndexOf(src, idx,
				wycsAttributes(branch)), code.assignedType());
	}

	protected void transform(Codes.Move code, VcBranch branch) {
		branch.write(code.target(), branch.read(code.operand(0)), code.assignedType());
	}

	protected void transform(Codes.NewMap code, VcBranch branch) {
		// TODO
		branch.invalidate(code.target(),code.type());
	}

	protected void transform(Codes.NewObject code, VcBranch branch) {
		// TODO
		branch.invalidate(code.target(),code.type());
	}

	protected void transform(Codes.Nop code, VcBranch branch) {
		// do nout
	}

	protected void transform(Codes.SubString code, VcBranch branch) {
		transformTernary(Expr.Ternary.Op.SUBLIST,code,branch);		
	}

	protected void transform(Codes.SubList code, VcBranch branch) {
		transformTernary(Expr.Ternary.Op.SUBLIST,code,branch);		
	}

	protected void transform(Codes.TupleLoad code, VcBranch branch) {
		Expr src = branch.read(code.operand(0));
		Expr index = new Expr.Constant(Value.Integer(BigInteger
				.valueOf(code.index)));
		Expr result = new Expr.IndexOf(src, index, wycsAttributes(branch));
		branch.write(code.target(), result, code.assignedType());
	}

	protected void transform(Codes.UnaryOperator code, VcBranch branch) {
		if (code.kind == Codes.UnaryOperatorKind.NEG) {
			transformUnary(Expr.Unary.Op.NEG,code,branch);			
		} else {
			// TODO
			branch.invalidate(code.target(),code.type());
		}
	}

	protected void transform(Codes.Update code, VcBranch branch) {
		Expr result = branch.read(code.result());
		Expr source = branch.read(code.target());
		branch.write(code.target(),
				updateHelper(code.iterator(), source, result, branch), code.assignedType());
	}

	protected Expr updateHelper(Iterator<Codes.LVal> iter, Expr source,
			Expr result, VcBranch branch) {
		if (!iter.hasNext()) {
			return result;
		} else {
			Collection<Attribute> attributes = wycsAttributes(branch);
			Codes.LVal lv = iter.next();
			if (lv instanceof Codes.RecordLVal) {
				Codes.RecordLVal rlv = (Codes.RecordLVal) lv;

				// FIXME: following is broken for open records.
				ArrayList<String> fields = new ArrayList<String>(rlv.rawType()
						.fields().keySet());
				Collections.sort(fields);
				int index = fields.indexOf(rlv.field);
				Expr[] operands = new Expr[fields.size()];
				for (int i = 0; i != fields.size(); ++i) {
					Expr _i = new Expr
							.Constant(Value.Integer(BigInteger.valueOf(i)));
					if (i != index) {
						operands[i] = new Expr.IndexOf(source, _i, attributes);
					} else {
						operands[i] = updateHelper(iter,
								new Expr.IndexOf(source, _i, attributes), result,
								branch);
					}
				}
				return new Expr.Nary(Expr.Nary.Op.TUPLE, operands, attributes);
			} else if (lv instanceof Codes.ListLVal) {
				Codes.ListLVal rlv = (Codes.ListLVal) lv;
				Expr index = branch.read(rlv.indexOperand);
				result = updateHelper(iter, new Expr.IndexOf(source, index,
						attributes), result, branch);
				return new Expr.Ternary(Expr.Ternary.Op.UPDATE, source, index,
						result, wycsAttributes(branch));
			} else if (lv instanceof Codes.MapLVal) {
				return source; // TODO
			} else if (lv instanceof Codes.StringLVal) {
				return source; // TODO
			} else {
				return source; // TODO
			}
		}
	}

	/**
	 * Transform an assignable unary bytecode using a given target operator.
	 * This must read the operand and then create the appropriate target
	 * expression. Finally, the result of the bytecode must be written back to
	 * the enclosing branch.
	 * 
	 * @param operator --- The target operator
	 * @param code --- The bytecode being translated
	 * @param branch --- The enclosing branch
	 */
	protected void transformUnary(Expr.Unary.Op operator,
			Code.AbstractUnaryAssignable code, VcBranch branch) {
		Expr lhs = branch.read(code.operand(0));

		branch.write(code.target(), new Expr.Unary(operator, lhs,
				wycsAttributes(branch)), code.assignedType());
	}
	
	/**
	 * Transform an assignable binary bytecode using a given target operator.
	 * This must read both operands and then create the appropriate target
	 * expression. Finally, the result of the bytecode must be written back to
	 * the enclosing branch.
	 * 
	 * @param operator --- The target operator
	 * @param code --- The bytecode being translated
	 * @param branch --- The enclosing branch
	 */
	protected void transformBinary(Expr.Binary.Op operator,
			Code.AbstractBinaryAssignable code, VcBranch branch) {
		Expr lhs = branch.read(code.operand(0));
		Expr rhs = branch.read(code.operand(1));

		branch.write(code.target(), new Expr.Binary(operator, lhs, rhs,
				wycsAttributes(branch)), code.assignedType());
	}
	
	/**
	 * Transform an assignable ternary bytecode using a given target operator.
	 * This must read all operands and then create the appropriate target
	 * expression. Finally, the result of the bytecode must be written back to
	 * the enclosing branch.
	 * 
	 * @param operator --- The target operator
	 * @param code --- The bytecode being translated
	 * @param branch --- The enclosing branch
	 */
	protected void transformTernary(Expr.Ternary.Op operator,
			Code.AbstractNaryAssignable code, VcBranch branch) {
		Expr one = branch.read(code.operand(0));
		Expr two = branch.read(code.operand(1));
		Expr three = branch.read(code.operand(2));		
		branch.write(code.target(), new Expr.Ternary(operator, one, two, three,
				wycsAttributes(branch)), code.assignedType());
	}
	
	/**
	 * Transform an assignable nary bytecode using a given target operator. This
	 * must read all operands and then create the appropriate target
	 * expression. Finally, the result of the bytecode must be written back to
	 * the enclosing branch.
	 * 
	 * @param operator
	 *            --- The target operator
	 * @param code
	 *            --- The bytecode being translated
	 * @param branch
	 *            --- The enclosing branch
	 */
	protected void transformNary(Expr.Nary.Op operator,
			Code.AbstractNaryAssignable code, VcBranch branch) {
		int[] code_operands = code.operands();
		Expr[] vals = new Expr[code_operands.length];
		for (int i = 0; i != vals.length; ++i) {
			vals[i] = branch.read(code_operands[i]);
		}
		branch.write(code.target(), new Expr.Nary(operator, vals,
				wycsAttributes(branch)), code.assignedType());
	}
	
	protected List<AttributedCodeBlock> findPrecondition(NameID name, Type.FunctionOrMethod fun,
			VcBranch branch) throws Exception {
		Path.Entry<WyilFile> e = builder.project().get(name.module(),
				WyilFile.ContentType);
		if (e == null) {
			syntaxError(
					errorMessage(ErrorMessages.RESOLUTION_ERROR, name.module()
							.toString()), filename, rootBlock.attributes(branch
							.pc()));
		}
		WyilFile m = e.read();
		WyilFile.FunctionOrMethodDeclaration method = m.functionOrMethod(name.name(), fun);

		for (WyilFile.Case c : method.cases()) {
			// FIXME: this is a hack for now
			return c.precondition();
		}

		return null;
	}

	protected List<AttributedCodeBlock> findPostcondition(NameID name,
			Type.FunctionOrMethod fun, VcBranch branch) throws Exception {
		Path.Entry<WyilFile> e = builder.project().get(name.module(),
				WyilFile.ContentType);
		if (e == null) {
			syntaxError(
					errorMessage(ErrorMessages.RESOLUTION_ERROR, name.module()
							.toString()), filename, rootBlock.attributes(branch.pc()));
		}
		WyilFile m = e.read();
		WyilFile.FunctionOrMethodDeclaration method = m.functionOrMethod(
				name.name(), fun);

		for (WyilFile.Case c : method.cases()) {
			// FIXME: this is a hack for now
			if(c.postcondition() != null && c.postcondition().size() > 0) {
				return c.postcondition();
			}
		}
		return Collections.EMPTY_LIST;
	}

	/**
	 * Generate a constraint representing an external block (e.g. a
	 * pre/post-condition or invariant).
	 *
	 * @param externalBlock
	 *            --- the external block of code being translated.
	 * @param prefix
	 *            --- a prefix to use to ensure that local variables to the
	 *            external block will not clash with variables in the branch.
	 * @param operands
	 *            --- operand register in containing branch which should map to
	 *            the inputs of the block being translated.
	 * @param branch
	 *            --- branch into which the resulting constraint is to be
	 *            placed.
	 * @return
	 */
	protected Expr transformExternalBlock(AttributedCodeBlock externalBlock,
			Expr[] operands, Type[] types, VcBranch branch) {

		// first, generate a constraint representing the post-condition.
		VcBranch master = new VcBranch(externalBlock,operands.length);

		AssertOrAssumeScope scope = new AssertOrAssumeScope(false, externalBlock.size(), Collections.EMPTY_LIST);
		master.scopes.add(scope);

		// second, set initial environment
		for (int i = 0; i != operands.length; ++i) {
			master.write(i, operands[i], types[i]);
		}

		Expr constraint = master.transform(new VcGenerator(builder, wycsFile,
				filename, true));

		return constraint;
	}
	
	/**
	 * Dispatch the branch to the next instruction in sequence. This can move
	 * the branch passed the end of the sequence.
	 * 
	 * @param branch
	 */
	public void gotoNext(VcBranch branch) {
		
	}
	
	public void gotoLabel(String label, VcBranch branch) {
		
	}
	
	/**
	 * Recursively descend the scope stack building up appropriate
	 * parameterisation of the core assertion as we go.
	 *
	 * @param index
	 *            --- current depth into the scope stack.
	 * @param implication
	 *            --- the core assertion being parameterised.
	 * @param uses
	 *            --- the set of (currently unparameterised) variables which are
	 *            used in the given expression.
	 * @param branch
	 *            --- current branch containing scope stack.
	 * @return
	 */
	protected Expr buildAssertion(int index, Expr implication,
			HashSet<String> uses, VcBranch branch) {
		if (index == branch.nScopes()) {
			return implication;
		} else {
			ArrayList<TypePattern> vars = new ArrayList<TypePattern>();
			Expr contents = buildAssertion(index + 1, implication, uses, branch);

			VcBranch.Scope scope = branch.scope(index);
			if (scope instanceof VcBranch.EntryScope) {
				VcBranch.EntryScope es = (VcBranch.EntryScope) scope;
				ArrayList<Type> parameters = es.declaration.type().params();
				for (int i = 0; i != parameters.size(); ++i) {
					Expr.Variable v = new Expr.Variable("r" + i);
					if (uses.contains(v.name)) {
						// only include variable if actually used
						uses.remove(v.name);
						SyntacticType t = convert(branch.typeOf(v.name),branch);
						vars.add(new TypePattern.Leaf(t, v));
					}
				}
				// Finally, scope any remaining free variables. Such variables
				// occur from modified operands of loops which are no longer on
				// the scope stack.
				for (String v : uses) {
					SyntacticType t = convert(branch.typeOf(v), branch);
					vars.add(new TypePattern.Leaf(t, new Expr.Variable(v)));
				}
			} else if (scope instanceof VcBranch.ForScope) {
				VcBranch.ForScope ls = (VcBranch.ForScope) scope;
				SyntacticType type = convert(ls.loop.type.element(), branch);

				// first, deal with index expression
				int[] modifiedOperands = ls.loop.modifiedOperands;
				if (uses.contains(ls.index.name)) {
					// only parameterise the index variable if it is actually
					// used.
					uses.remove(ls.index.name);

					Expr idx;
					if (ls.loop.type instanceof Type.EffectiveList) {
						// FIXME: hack to work around limitations of whiley for
						// loops.
						String i = "i" + indexCount++;
						vars.add(new TypePattern.Leaf(new SyntacticType.Int(),
								new Expr.Variable(i)));
						vars.add(new TypePattern.Leaf(type, ls.index));
						idx = new Expr.Nary(Expr.Nary.Op.TUPLE,
								new Expr[] { new Expr.Variable(i), ls.index });
					} else {
						vars.add(new TypePattern.Leaf(type, ls.index));
						idx = ls.index;
					}

					// since index is used, we need to imply that it is
					// contained in the source expression.
					contents = new Expr.Binary(Expr.Binary.Op.IMPLIES,
							new Expr.Binary(Expr.Binary.Op.IN, idx, ls.source),
							contents);
					//
					ls.source.freeVariables(uses); // updated uses appropriately
				}

				// second, deal with modified operands
				for (int i = 0; i != modifiedOperands.length; ++i) {
					int reg = modifiedOperands[i];
					Expr.Variable v = new Expr.Variable("r" + reg);
					if (uses.contains(v.name)) {
						// Only parameterise a modified operand if it is
						// actually used.
						uses.remove(v.name);
						SyntacticType t = convert(branch.typeOf(v.name),branch);
						vars.add(new TypePattern.Leaf(t, v));
					}
				}

			} else if (scope instanceof VcBranch.LoopScope) {
				VcBranch.LoopScope ls = (VcBranch.LoopScope) scope;
				// now, deal with modified operands
				int[] modifiedOperands = ls.loop.modifiedOperands;
				for (int i = 0; i != modifiedOperands.length; ++i) {
					int reg = modifiedOperands[i];
					Expr.Variable v = new Expr.Variable("r" + reg);
					if (uses.contains(v.name)) {
						// Only parameterise a modified operand if it is
						// actually used.
						uses.remove(v.name);
						SyntacticType t = convert(branch.typeOf(v.name),branch);
						vars.add(new TypePattern.Leaf(t, v));
					}
				}
			}

			if (vars.size() == 0) {
				// we have nothing to parameterise, so ignore it.
				return contents;
			} else if(vars.size() == 1){
				return new Expr.ForAll(vars.get(0),contents);
			} else {
				return new Expr.ForAll(new TypePattern.Tuple(vars), contents);
			}
		}
	}

	/**
	 * Generate a formula representing a condition from an Codes.IfCode or
	 * Codes.Assert bytecodes.
	 *
	 * @param op
	 * @param stack
	 * @param elem
	 * @return
	 */
	private Expr.Binary buildTest(Codes.Comparator cop, int leftOperand,
			int rightOperand, Type type, VcBranch branch) {
		Expr lhs = branch.read(leftOperand);
		Expr rhs = branch.read(rightOperand);
		Expr.Binary.Op op;
		switch (cop) {
		case EQ:
			op = Expr.Binary.Op.EQ;
			break;
		case NEQ:
			op = Expr.Binary.Op.NEQ;
			break;
		case GTEQ:
			op = Expr.Binary.Op.GTEQ;
			break;
		case GT:
			op = Expr.Binary.Op.GT;
			break;
		case LTEQ:
			op = Expr.Binary.Op.LTEQ;
			break;
		case LT:
			op = Expr.Binary.Op.LT;
			break;
		case SUBSET:
			op = Expr.Binary.Op.SUBSET;
			break;
		case SUBSETEQ:
			op = Expr.Binary.Op.SUBSETEQ;
			break;
		case IN:
			op = Expr.Binary.Op.IN;
			break;
		default:
			internalFailure("unknown comparator (" + cop + ")", filename,
					rootBlock.attributes(branch.pc()));
			return null;
		}

		return new Expr.Binary(op, lhs, rhs, wycsAttributes(branch));
	}

	/**
	 * Generate the logically inverted expression corresponding to this
	 * comparator.
	 *
	 * @param cop
	 * @param leftOperand
	 * @param rightOperand
	 * @param type
	 * @param branch
	 * @return
	 */
	private Expr invert(Expr.Binary test) {
		Expr.Binary.Op op;
		switch (test.op) {
		case EQ:
			op = Expr.Binary.Op.NEQ;
			break;
		case NEQ:
			op = Expr.Binary.Op.EQ;
			break;
		case GTEQ:
			op = Expr.Binary.Op.LT;
			break;
		case GT:
			op = Expr.Binary.Op.LTEQ;
			break;
		case LTEQ:
			op = Expr.Binary.Op.GT;
			break;
		case LT:
			op = Expr.Binary.Op.GTEQ;
			break;
		case SUBSET:
		case SUBSETEQ:
		case SUPSET:
		case SUPSETEQ:
		case IN:
			// NOTE: it's tempting to think that inverting x SUBSET y should
			// give x SUPSETEQ y, but this is not correct. See #423.
			op = Expr.Binary.Op.IN;
			return new Expr.Unary(Expr.Unary.Op.NOT, new Expr.Binary(test.op,
					test.leftOperand, test.rightOperand, test.attributes()),
					test.attributes());
		default:
			wycc.lang.SyntaxError.internalFailure("unknown comparator ("
					+ test.op + ")", filename, test);
			return null;
		}

		return new Expr.Binary(op, test.leftOperand, test.rightOperand,
				test.attributes());
	}

	public Value convert(Constant c, VcBranch branch) {
		if (c instanceof Constant.Null) {
			// TODO: is this the best translation?
			return wycs.core.Value.Integer(BigInteger.ZERO);
		} else if (c instanceof Constant.Bool) {
			Constant.Bool cb = (Constant.Bool) c;
			return wycs.core.Value.Bool(cb.value);
		} else if (c instanceof Constant.Byte) {
			Constant.Byte cb = (Constant.Byte) c;
			return wycs.core.Value.Integer(BigInteger.valueOf(cb.value));
		} else if (c instanceof Constant.Char) {
			Constant.Char cb = (Constant.Char) c;
			return wycs.core.Value.Integer(BigInteger.valueOf(cb.value));
		} else if (c instanceof Constant.Integer) {
			Constant.Integer cb = (Constant.Integer) c;
			return wycs.core.Value.Integer(cb.value);
		} else if (c instanceof Constant.Decimal) {
			Constant.Decimal cb = (Constant.Decimal) c;
			return wycs.core.Value.Decimal(cb.value);
		} else if (c instanceof Constant.Strung) {
			Constant.Strung cb = (Constant.Strung) c;
			String str = cb.value;
			ArrayList<Value> pairs = new ArrayList<Value>();
			for (int i = 0; i != str.length(); ++i) {
				ArrayList<Value> pair = new ArrayList<Value>();
				pair.add(Value.Integer(BigInteger.valueOf(i)));
				pair.add(Value.Integer(BigInteger.valueOf(str.charAt(i))));
				pairs.add(Value.Tuple(pair));
			}
			return Value.Set(pairs);
		} else if (c instanceof Constant.List) {
			Constant.List cb = (Constant.List) c;
			List<Constant> cb_values = cb.values;
			ArrayList<Value> pairs = new ArrayList<Value>();
			for (int i = 0; i != cb_values.size(); ++i) {
				ArrayList<Value> pair = new ArrayList<Value>();
				pair.add(Value.Integer(BigInteger.valueOf(i)));
				pair.add(convert(cb_values.get(i), branch));
				pairs.add(Value.Tuple(pair));
			}
			return Value.Set(pairs);
		} else if (c instanceof Constant.Map) {
			Constant.Map cb = (Constant.Map) c;
			ArrayList<Value> pairs = new ArrayList<Value>();
			for (Map.Entry<Constant, Constant> e : cb.values.entrySet()) {
				ArrayList<Value> pair = new ArrayList<Value>();
				pair.add(convert(e.getKey(), branch));
				pair.add(convert(e.getValue(), branch));
				pairs.add(Value.Tuple(pair));
			}
			return Value.Set(pairs);
		} else if (c instanceof Constant.Set) {
			Constant.Set cb = (Constant.Set) c;
			ArrayList<Value> values = new ArrayList<Value>();
			for (Constant v : cb.values) {
				values.add(convert(v, branch));
			}
			return wycs.core.Value.Set(values);
		} else if (c instanceof Constant.Tuple) {
			Constant.Tuple cb = (Constant.Tuple) c;
			ArrayList<Value> values = new ArrayList<Value>();
			for (Constant v : cb.values) {
				values.add(convert(v, branch));
			}
			return wycs.core.Value.Tuple(values);
		} else if (c instanceof Constant.Record) {
			Constant.Record rb = (Constant.Record) c;

			// NOTE:: records are currently translated into WyCS as tuples,
			// where
			// each field is allocated a slot based on an alphabetical sorting
			// of field names. It's unclear at this stage whether or not that is
			// a general solution. In particular, it would seem to be brokwn for
			// type testing.

			ArrayList<String> fields = new ArrayList<String>(rb.values.keySet());
			Collections.sort(fields);
			ArrayList<Value> values = new ArrayList<Value>();
			for (String field : fields) {
				values.add(convert(rb.values.get(field), branch));
			}
			return wycs.core.Value.Tuple(values);
		} else {
			internalFailure("unknown constant encountered (" + c + ")",
					filename, rootBlock.attributes(branch.pc()));
			return null;
		}
	}

	private SyntacticType convert(List<Type> types,
			VcBranch branch) {
		ArrayList<SyntacticType> ntypes = new ArrayList<SyntacticType>();
		for(int i=0;i!=types.size();++i) {
			ntypes.add(convert(types.get(i),branch));
		}
		return new SyntacticType.Tuple(ntypes);
	}

	private SyntacticType convert(Type t, VcBranch branch) {
		// FIXME: this is fundamentally broken in the case of recursive types.
		// See Issue #298.
		if (t instanceof Type.Any) {
			return new SyntacticType.Any(wycsAttributes(branch));
		} else if (t instanceof Type.Void) {
			return new SyntacticType.Void(wycsAttributes(branch));
		} else if (t instanceof Type.Null) {
			// FIXME: implement SyntacticType.Null
			//return new SyntacticType.Null(attributes(branch));
			return new SyntacticType.Any(wycsAttributes(branch));
		} else if (t instanceof Type.Bool) {
			return new SyntacticType.Bool(wycsAttributes(branch));
		} else if (t instanceof Type.Char) {
			// FIXME: implement SyntacticType.Char
			//return new SyntacticType.Char(attributes(branch));
			return new SyntacticType.Int(wycsAttributes(branch));
		} else if (t instanceof Type.Byte) {
			// FIXME: implement SyntacticType.Byte
			//return new SyntacticType.Byte(attributes(branch));
			return new SyntacticType.Int(wycsAttributes(branch));
		} else if (t instanceof Type.Int) {
			return new SyntacticType.Int(wycsAttributes(branch));
		} else if (t instanceof Type.Real) {
			return new SyntacticType.Real(wycsAttributes(branch));
		} else if (t instanceof Type.Strung) {
			// FIXME: implement SyntacticType.Strung
			//return new SyntacticType.Strung(attributes(branch));
			return new SyntacticType.List(new SyntacticType.Int(wycsAttributes(branch)));
		} else if (t instanceof Type.Set) {
			Type.Set st = (Type.Set) t;
			SyntacticType element = convert(st.element(), branch);
			return new SyntacticType.Set(element);
		} else if (t instanceof Type.Map) {
			Type.Map lt = (Type.Map) t;
			SyntacticType from = convert(lt.key(), branch);
			SyntacticType to = convert(lt.value(), branch);
			// ugly.
			return new SyntacticType.Map(from,to);
		} else if (t instanceof Type.List) {
			Type.List lt = (Type.List) t;
			SyntacticType element = convert(lt.element(), branch);
			// ugly.
			return new SyntacticType.List(element);
		} else if (t instanceof Type.Tuple) {
			Type.Tuple tt = (Type.Tuple) t;
			ArrayList<SyntacticType> elements = new ArrayList<SyntacticType>();
			for (int i = 0; i != tt.size(); ++i) {
				elements.add(convert(tt.element(i), branch));
			}
			return new SyntacticType.Tuple(elements);
		} else if (t instanceof Type.Record) {
			Type.Record rt = (Type.Record) t;
			HashMap<String, Type> fields = rt.fields();
			ArrayList<String> names = new ArrayList<String>(fields.keySet());
			ArrayList<SyntacticType> elements = new ArrayList<SyntacticType>();
			Collections.sort(names);
			for (int i = 0; i != names.size(); ++i) {
				String field = names.get(i);
				elements.add(convert(fields.get(field), branch));
			}
			return new SyntacticType.Tuple(elements);
		} else if (t instanceof Type.Reference) {
			// FIXME: how to translate this??
			return new SyntacticType.Any();
		} else if (t instanceof Type.Union) {
			Type.Union tu = (Type.Union) t;
			HashSet<Type> tu_elements = tu.bounds();
			ArrayList<SyntacticType> elements = new ArrayList<SyntacticType>();
			for (Type te : tu_elements) {
				elements.add(convert(te, branch));
			}
			return new SyntacticType.Union(elements);
		} else if (t instanceof Type.Negation) {
			Type.Negation nt = (Type.Negation) t;
			SyntacticType element = convert(nt.element(), branch);
			return new SyntacticType.Negation(element);
		} else if (t instanceof Type.FunctionOrMethod) {
			Type.FunctionOrMethod ft = (Type.FunctionOrMethod) t;
			return new SyntacticType.Any();
		} else {
			internalFailure("unknown type encountered ("
					+ t.getClass().getName() + ")", filename,
					rootBlock.attributes(branch.pc()));
			return null;
		}
	}

	private Expr and(List<Expr> constraints) {
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

	/**
	 * Convert a wyil NameID into a string that is suitable to be used as a
	 * function name or variable identifier in WycsFiles.
	 *
	 * @param id
	 * @return
	 */
	private String toIdentifier(NameID id) {
		return id.toString().replace(":","_").replace("/","_");
	}

	/**
	 * Convert the attributes at the current location in a given branch into
	 * those appropriate for WyCS.
	 * 
	 * @param branch
	 * @return
	 */
	private static Collection<wycc.lang.Attribute> wycsAttributes(
			VcBranch branch) {
		// FIXME: to do!
		return Collections.EMPTY_LIST;
	}
	
	
}

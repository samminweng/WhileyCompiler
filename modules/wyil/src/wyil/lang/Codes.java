package wyil.lang;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import wycc.lang.NameID;
import wycc.util.Pair;
import wyil.lang.Code.*;
import static wyil.lang.Code.*;
import static wyil.lang.CodeUtils.*;

public abstract class Codes {

	/**
	 * Provided to aid readability of client code.
	 */
	public final static int NULL_REG = -1;
	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_0 = 0;
	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_1 = 1;
	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_2 = 2;
	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_3 = 3;
	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_4 = 4;
	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_5 = 5;
	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_6 = 6;

	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_7 = 7;

	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_8 = 8;

	/**
	 * Provided to aid readability of client code.
	 */
	public final static int REG_9 = 9;

	// ===============================================================
	// Bytecode Constructors
	// ===============================================================

	/**
	 * Construct an <code>assert</code> bytecode which represents a user-defined
	 * assertion check.
	 *
	 * @param message
	 *            --- message to report upon failure.
	 * @return
	 */
	public static Assert Assert(String target) {
		return Codes.get(new Assert(target));
	}

	/**
	 * Construct an <code>assume</code> bytecode which represents a user-defined
	 * assumption.
	 *
	 * @param message
	 *            --- message to report upon failure.
	 * @return
	 */
	public static Assume Assume(String target) {
		return Codes.get(new Assume(target));
	}

	public static BinaryOperator BinaryOperator(Type type, int target, int leftOperand,
			int rightOperand, BinaryOperatorKind op) {
		return Codes.get(new BinaryOperator(type, target, leftOperand,
				rightOperand, op));
	}

	/**
	 * Construct a <code>const</code> bytecode which loads a given constant onto
	 * the stack.
	 *
	 * @param afterType
	 *            --- record type.
	 * @param field
	 *            --- field to write.
	 * @return
	 */
	public static Const Const(int target, Constant constant) {
		return Codes.get(new Const(target, constant));
	}

	/**
	 * Construct a <code>copy</code> bytecode which copies the value from a
	 * given operand register into a given target register.
	 *
	 * @param type
	 *            --- record type.
	 * @param reg
	 *            --- reg to load.
	 * @return
	 */
	public static Assign Assign(Type type, int target, int operand) {
		return Codes.get(new Assign(type, target, operand));
	}

	public static Convert Convert(Type from, int target, int operand, Type to) {
		return Codes.get(new Convert(from, target, operand, to));
	}

	public static final Debug Debug(int operand) {
		return Codes.get(new Debug(operand));
	}

	public static LoopEnd LoopEnd(String label) {
		return Codes.get(new LoopEnd(label));
	}

	/**
	 * Construct a <code>fail</code> bytecode which halts execution by raising a
	 * fault.
	 *
	 * @param string
	 *            --- Message to give on error.
	 * @return
	 */
	public static Fail Fail(String message) {
		return Codes.get(new Fail(message));
	}

	/**
	 * Construct a <code>fieldload</code> bytecode which reads a given field
	 * from a record of a given type.
	 *
	 * @param type
	 *            --- record type.
	 * @param field
	 *            --- field to load.
	 * @return
	 */
	public static FieldLoad FieldLoad(Type.EffectiveRecord type, int target,
			int operand, String field) {
		return Codes.get(new FieldLoad(type, target, operand, field));
	}

	/**
	 * Construct a <code>goto</code> bytecode which branches unconditionally to
	 * a given label.
	 *
	 * @param label
	 *            --- destination label.
	 * @return
	 */
	public static Goto Goto(String label) {
		return Codes.get(new Goto(label));
	}

	public static Invoke Invoke(Type.FunctionOrMethod fun, int target,
			Collection<Integer> operands, NameID name) {
		return Codes.get(new Invoke(fun, target, CodeUtils.toIntArray(operands), name));
	}

	public static Invoke Invoke(Type.FunctionOrMethod fun, int target,
			int[] operands, NameID name) {
		return Codes.get(new Invoke(fun, target, operands, name));
	}

	public static Lambda Lambda(Type.FunctionOrMethod fun, int target,
			Collection<Integer> operands, NameID name) {
		return Codes.get(new Lambda(fun, target, CodeUtils.toIntArray(operands), name));
	}

	public static Lambda Lambda(Type.FunctionOrMethod fun, int target,
			int[] operands, NameID name) {
		return Codes.get(new Lambda(fun, target, operands, name));
	}

	public static Not Not(int target, int operand) {
		return Codes.get(new Not(target, operand));
	}

	public static LengthOf LengthOf(Type.EffectiveCollection type, int target,
			int operand) {
		return Codes.get(new LengthOf(type, target, operand));
	}

	public static Move Move(Type type, int target, int operand) {
		return Codes.get(new Move(type, target, operand));
	}

	public static SubList SubList(Type.EffectiveList type, int target,
			int sourceOperand, int leftOperand, int rightOperand) {
		int[] operands = new int[] { sourceOperand, leftOperand, rightOperand };
		return Codes.get(new SubList(type, target, operands));
	}

	public static SubList SubList(Type.EffectiveList type, int target,
			int[] operands) {
		return Codes.get(new SubList(type, target, operands));
	}

	public static ListOperator ListOperator(Type.EffectiveList type, int target,
			int leftOperand, int rightOperand, ListOperatorKind dir) {
		return Codes.get(new ListOperator(type, target, leftOperand, rightOperand,
				dir));
	}

	/**
	 * Construct a <code>listload</code> bytecode which reads a value from a
	 * given index in a given list.
	 *
	 * @param type
	 *            --- list type.
	 * @return
	 */
	public static IndexOf IndexOf(Type.EffectiveIndexible type, int target,
			int leftOperand, int rightOperand) {
		return Codes.get(new IndexOf(type, target, leftOperand, rightOperand));
	}

	public static Loop Loop(String label, Collection<Integer> operands) {
		return Codes.get(new Loop(label, CodeUtils.toIntArray(operands)));
	}

	public static Loop Loop(String label, int[] modifies) {
		return Codes.get(new Loop(label, modifies));
	}

	public static ForAll ForAll(Type.EffectiveCollection type,
			int sourceOperand, int indexOperand,
			Collection<Integer> modifiedOperands, String label) {
		return Codes.get(new ForAll(type, sourceOperand, indexOperand,
				CodeUtils.toIntArray(modifiedOperands), label));
	}

	public static ForAll ForAll(Type.EffectiveCollection type,
			int sourceOperand, int indexOperand, int[] modifiedOperands,
			String label) {
		return Codes.get(new ForAll(type, sourceOperand, indexOperand,
				modifiedOperands, label));
	}

	/**
	 * Construct a <code>newdict</code> bytecode which constructs a new map and
	 * puts it on the stack.
	 *
	 * @param type
	 * @return
	 */
	public static NewMap NewMap(Type.Map type, int target,
			Collection<Integer> operands) {
		return Codes.get(new NewMap(type, target, CodeUtils.toIntArray(operands)));
	}

	public static NewMap NewMap(Type.Map type, int target, int[] operands) {
		return Codes.get(new NewMap(type, target, operands));
	}

	/**
	 * Construct a <code>newset</code> bytecode which constructs a new set and
	 * puts it on the stack.
	 *
	 * @param type
	 * @return
	 */
	public static NewSet NewSet(Type.Set type, int target,
			Collection<Integer> operands) {
		return Codes.get(new NewSet(type, target, CodeUtils.toIntArray(operands)));
	}

	public static NewSet NewSet(Type.Set type, int target, int[] operands) {
		return Codes.get(new NewSet(type, target, operands));
	}

	/**
	 * Construct a <code>newlist</code> bytecode which constructs a new list and
	 * puts it on the stack.
	 *
	 * @param type
	 * @return
	 */
	public static NewList NewList(Type.List type, int target,
			Collection<Integer> operands) {
		return Codes.get(new NewList(type, target, CodeUtils.toIntArray(operands)));
	}

	public static NewList NewList(Type.List type, int target, int[] operands) {
		return Codes.get(new NewList(type, target, operands));
	}

	/**
	 * Construct a <code>newtuple</code> bytecode which constructs a new tuple
	 * and puts it on the stack.
	 *
	 * @param type
	 * @return
	 */
	public static NewTuple NewTuple(Type.Tuple type, int target,
			Collection<Integer> operands) {
		return Codes.get(new NewTuple(type, target, CodeUtils.toIntArray(operands)));
	}

	public static NewTuple NewTuple(Type.Tuple type, int target, int[] operands) {
		return Codes.get(new NewTuple(type, target, operands));
	}

	/**
	 * Construct a <code>newrecord</code> bytecode which constructs a new record
	 * and puts it on the stack.
	 *
	 * @param type
	 * @return
	 */
	public static NewRecord NewRecord(Type.Record type, int target,
			Collection<Integer> operands) {
		return Codes.get(new NewRecord(type, target, CodeUtils.toIntArray(operands)));
	}

	public static NewRecord NewRecord(Type.Record type, int target,
			int[] operands) {
		return Codes.get(new NewRecord(type, target, operands));
	}

	/**
	 * Construct a return bytecode which does return a value and, hence, its
	 * type automatically defaults to void.
	 *
	 * @return
	 */
	public static Return Return() {
		return Codes.get(new Return(Type.T_VOID, Codes.NULL_REG));
	}

	/**
	 * Construct a return bytecode which reads a value from the operand register
	 * and returns it.
	 *
	 * @param type
	 *            --- type of the value to be returned (cannot be void).
	 * @param operand
	 *            --- register to read return value from.
	 * @return
	 */
	public static Return Return(Type type, int operand) {
		return Codes.get(new Return(type, operand));
	}

	public static If If(Type type, int leftOperand, int rightOperand,
			Comparator cop, String label) {
		return Codes.get(new If(type, leftOperand, rightOperand, cop, label));
	}

	public static IfIs IfIs(Type type, int leftOperand, Type rightOperand,
			String label) {
		return Codes.get(new IfIs(type, leftOperand, rightOperand, label));
	}

	public static IndirectInvoke IndirectInvoke(Type.FunctionOrMethod fun,
			int target, int operand, Collection<Integer> operands) {
		return Codes.get(new IndirectInvoke(fun, target, operand, CodeUtils
				.toIntArray(operands)));
	}

	public static IndirectInvoke IndirectInvoke(Type.FunctionOrMethod fun,
			int target, int operand, int[] operands) {
		return Codes.get(new IndirectInvoke(fun, target, operand, operands));
	}

	public static Invert Invert(Type type, int target, int operand) {
		return Codes.get(new Invert(type, target, operand));
	}

	public static Label Label(String label) {
		return Codes.get(new Label(label));
	}

	public static final Nop Nop = new Nop();

	public static SetOperator SetOperator(Type.EffectiveSet type, int target,
			int leftOperand, int rightOperand, SetOperatorKind operation) {
		return Codes.get(new SetOperator(type, target, leftOperand, rightOperand,
				operation));
	}

	public static StringOperator StringOperator(int target, int leftOperand,
			int rightOperand, StringOperatorKind operation) {
		return Codes.get(new StringOperator(target, leftOperand, rightOperand,
				operation));
	}

	public static SubString SubString(int target, int sourceOperand,
			int leftOperand, int rightOperand) {
		int[] operands = new int[] { sourceOperand, leftOperand, rightOperand };
		return Codes.get(new SubString(target, operands));
	}

	private static SubString SubString(int target, int[] operands) {
		return Codes.get(new SubString(target, operands));
	}

	/**
	 * Construct a <code>switch</code> bytecode which pops a value off the
	 * stack, and switches to a given label based on it.
	 *
	 * @param type
	 *            --- value type to switch on.
	 * @param defaultLabel
	 *            --- target for the default case.
	 * @param cases
	 *            --- map from values to destination labels.
	 * @return
	 */
	public static Switch Switch(Type type, int operand, String defaultLabel,
			Collection<Pair<Constant, String>> cases) {
		return Codes.get(new Switch(type, operand, defaultLabel, cases));
	}

	/**
	 * Construct a <code>throw</code> bytecode which pops a value off the stack
	 * and throws it.
	 *
	 * @param afterType
	 *            --- value type to throw
	 * @return
	 */
	public static Throw Throw(Type type, int operand) {
		return Codes.get(new Throw(type, operand));
	}

	/**
	 * Construct a <code>trycatch</code> bytecode which defines a region of
	 * bytecodes which are covered by one or more catch handles.
	 *
	 * @param target
	 *            --- identifies end-of-block label.
	 * @param catches
	 *            --- map from types to destination labels.
	 * @return
	 */
	public static TryCatch TryCatch(int operand, String target,
			Collection<Pair<Type, String>> catches) {
		return Codes.get(new TryCatch(operand, target, catches));
	}

	public static TryEnd TryEnd(String label) {
		return Codes.get(new TryEnd(label));
	}

	public static TupleLoad TupleLoad(Type.EffectiveTuple type, int target,
			int operand, int index) {
		return Codes.get(new TupleLoad(type, target, operand, index));
	}

	public static NewObject NewObject(Type.Reference type, int target,
			int operand) {
		return Codes.get(new NewObject(type, target, operand));
	}

	public static Dereference Dereference(Type.Reference type, int target,
			int operand) {
		return Codes.get(new Dereference(type, target, operand));
	}

	public static Update Update(Type beforeType, int target,
			Collection<Integer> operands, int operand, Type afterType,
			Collection<String> fields) {
		return Codes.get(new Update(beforeType, target,
				CodeUtils.toIntArray(operands), operand, afterType, fields));
	}

	public static Update Update(Type beforeType, int target, int[] operands,
			int operand, Type afterType, Collection<String> fields) {
		return Codes.get(new Update(beforeType, target, operands, operand,
				afterType, fields));
	}

	public static UnaryOperator UnaryOperator(Type type, int target, int operand,
			UnaryOperatorKind uop) {
		return Codes.get(new UnaryOperator(type, target, operand, uop));
	}

	public static Void Void(Type type, int[] operands) {
		return Codes.get(new Void(type, operands));
	}

	// ===============================================================
	// Bytecode Implementations
	// ===============================================================

	/**
	 * Represents a binary operator (e.g. '+','-',etc) that is provided to a
	 * <code>BinOp</code> bytecode.
	 *
	 * @author David J. Pearce
	 *
	 */
	public enum BinaryOperatorKind {
		ADD(0) {
			public String toString() {
				return "add";
			}
		},
		SUB(1) {
			public String toString() {
				return "sub";
			}
		},
		MUL(2) {
			public String toString() {
				return "mul";
			}
		},
		DIV(3) {
			public String toString() {
				return "div";
			}
		},
		REM(4) {
			public String toString() {
				return "rem";
			}
		},
		RANGE(5) {
			public String toString() {
				return "range";
			}
		},
		BITWISEOR(6) {
			public String toString() {
				return "or";
			}
		},
		BITWISEXOR(7) {
			public String toString() {
				return "xor";
			}
		},
		BITWISEAND(8) {
			public String toString() {
				return "and";
			}
		},
		LEFTSHIFT(9) {
			public String toString() {
				return "shl";
			}
		},
		RIGHTSHIFT(10) {
			public String toString() {
				return "shr";
			}
		};
		public int offset;

		private BinaryOperatorKind(int offset) {
			this.offset = offset;
		}
	};

	/**
	 * <p>
	 * A binary operation which reads two numeric values from the operand
	 * registers, performs an operation on them and writes the result to the
	 * target register. The binary operators are:
	 * </p>
	 * <ul>
	 * <li><i>add, subtract, multiply, divide, remainder</i>. Both operands must
	 * be either integers or reals (but not one or the other). A value of the
	 * same type is produced.</li>
	 * <li><i>range</i></li>
	 * <li><i>bitwiseor, bitwisexor, bitwiseand</i></li>
	 * <li><i>leftshift,rightshift</i></li>
	 * </ul>
	 * For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 *     return ((x * y) + 1) / 2
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 * body:
	 *     mul %2 = %0, %1   : int
	 *     const %3 = 1      : int
	 *     add %2 = %2, %3   : int
	 *     const %3 = 2      : int
	 *     const %4 = 0      : int
	 *     assertne %3, %4 "division by zero" : int
	 *     div %2 = %2, %3   : int
	 *     return %2         : int
	 * </pre>
	 *
	 * Here, the <code>assertne</code> bytecode has been included to check
	 * against division-by-zero. In this particular case the assertion is known
	 * true at compile time and, in practice, would be compiled away.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class BinaryOperator extends AbstractBinaryAssignable<Type> {
		public final BinaryOperatorKind kind;

		private BinaryOperator(Type type, int target, int lhs, int rhs,
				BinaryOperatorKind bop) {
			super(type, target, lhs, rhs);
			if (bop == null) {
				throw new IllegalArgumentException(
						"BinOp bop argument cannot be null");
			}
			this.kind = bop;
		}

		@Override
		public int opcode() {
			return OPCODE_add + kind.offset;
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return BinaryOperator(type(), nTarget, nOperands[0], nOperands[1],
					kind);
		}

		public int hashCode() {
			return kind.hashCode() + super.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof BinaryOperator) {
				BinaryOperator bo = (BinaryOperator) o;
				return kind.equals(bo.kind) && super.equals(bo);
			}
			return false;
		}

		public String toString() {
			return kind + " %" + target() + " = %" + operand(0) + ", %"
					+ operand(1) + " : " + type();
		}
	}

	/**
	 * Reads a value from the operand register, converts it to a given type and
	 * writes the result to the target register. This bytecode is the only way
	 * to change the type of a value. It's purpose is to simplify
	 * implementations which have different representations of data types. A
	 * convert bytecode must be inserted whenever the type of a register
	 * changes. This includes at control-flow meet points, when the value is
	 * passed as a parameter, assigned to a field, etc. For example, the
	 * following Whiley code:
	 *
	 * <pre>
	 * function f(int x) => real:
	 *     return x + 1
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x) => real:
	 * body:
	 *     const %2 = 1           : int
	 *     add %1 = %0, %2        : int
	 *     convert %1 = %1 real   : int
	 *     return %1              : real
	 * </pre>
	 * <p>
	 * Here, we see that the <code>int</code> value in register <code>%1</code>
	 * must be explicitly converted into a <code>real</code> value before it can
	 * be returned from this function.
	 * </p>
	 * <p>
	 * <b>NOTE:</b> In many cases, this bytecode may correspond to a nop on the
	 * hardware. Consider converting from <code>[any]</code> to <code>any</code>
	 * . On the JVM, <code>any</code> translates to <code>Object</code>, whilst
	 * <code>[any]</code> translates to <code>List</code> (which is an instance
	 * of <code>Object</code>). Thus, no conversion is necessary since
	 * <code>List</code> can safely flow into <code>Object</code>.
	 * </p>
	 *
	 */
	public static final class Convert extends AbstractUnaryAssignable<Type> {
		public final Type result;

		private Convert(Type from, int target, int operand, Type result) {
			super(from, target, operand);
			if (result == null) {
				throw new IllegalArgumentException(
						"Convert to argument cannot be null");
			}
			this.result = result;
		}

		public Code.Unit clone(int nTarget, int[] nOperands) {
			return Convert(type(), nTarget, nOperands[0], result);
		}

		public int opcode() {
			return OPCODE_convert;
		}

		public int hashCode() {
			return result.hashCode() + super.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof Convert) {
				Convert c = (Convert) o;
				return super.equals(c) && result.equals(c.result);
			}
			return false;
		}

		public String toString() {
			return "convert %" + target() + " = %" + operand(0) + " " + result
					+ " : " + type();
		}
	}

	/**
	 * Writes a constant value to a target register. This includes
	 * <i>integers</i>, <i>rationals</i>, <i>lists</i>, <i>sets</i>,
	 * <i>maps</i>, etc. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 *     xs = {1,2.12}
	 *     return |xs| + 1
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 * body:
	 *     var xs
	 *     const %2 = 1               : int
	 *     convert %2 = % 2 int|real  : int
	 *     const %3 = 2.12            : real
	 *     convert %3 = % 3 int|real  : real
	 *     newset %1 = (%2, %3)       : {int|real}
	 *     assign %3 = %1             : {int|real}
	 *     lengthof %3 = % 3          : {int|real}
	 *     const %4 = 1               : int
	 *     add %2 = % 3, %4           : int
	 *     return %2                  : int
	 * </pre>
	 *
	 * Here, we see two kinds of constants values being used: integers (i.e.
	 * <code>const %2 = 1</code>) and rationals (i.e.
	 * <code>const %3 = 2.12</code>).
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Const extends AbstractAssignable {
		public final Constant constant;

		private Const(int target, Constant constant) {
			super(target);
			this.constant = constant;
		}

		public int opcode() {
			return OPCODE_const;
		}

		@Override
		public void registers(java.util.Set<Integer> registers) {
			registers.add(target());
		}

		@Override
		public Code.Unit remap(Map<Integer, Integer> binding) {
			Integer nTarget = binding.get(target());
			if (nTarget != null) {
				return Const(nTarget, constant);
			}
			return this;
		}

		public Type assignedType() {
			return (Type) constant.type();
		}

		public int hashCode() {
			return constant.hashCode() + target();
		}

		public boolean equals(Object o) {
			if (o instanceof Const) {
				Const c = (Const) o;
				return constant.equals(c.constant) && target() == c.target();
			}
			return false;
		}

		public String toString() {
			return "const %" + target() + " = " + constant + " : "
					+ constant.type();
		}
	}

	/**
	 * Copy the contents from a given operand register into a given target
	 * register. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 *     x = x + 1
	 *     return x
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 * body:
	 *     assign %1 = %0      : int
	 *     const %2 = 1        : int
	 *     add %0 = %1, %2     : int
	 *     return %0           : int
	 * </pre>
	 *
	 * Here we see that an initial assignment is made from register
	 * <code>%0</code> to register <code>%1</code>. In fact, this assignment is
	 * unecessary but is useful to illustrate the <code>assign</code> bytecode.
	 *
	 * <p>
	 * <b>NOTE:</b> on many architectures this operation may not actually clone
	 * the data in question. Rather, it may copy the <i>reference</i> to the
	 * data and then increment its <i>reference count</i>. This is to ensure
	 * efficient treatment of large compound structures (e.g. lists, sets, maps
	 * and records).
	 * </p>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Assign extends AbstractUnaryAssignable<Type> {

		private Assign(Type type, int target, int operand) {
			super(type, target, operand);
		}

		public int opcode() {
			return OPCODE_assign;
		}

		public Code.Unit clone(int nTarget, int[] nOperands) {
			return Assign(type(), nTarget, nOperands[0]);
		}

		public boolean equals(Object o) {
			if (o instanceof Assign) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "assign %" + target() + " = %" + operand(0) + " " + " : " + type();
		}
	}

	/**
	 * Read a string from the operand register and prints it to the debug
	 * console. For example, the following Whiley code:
	 *
	 * <pre>
	 * method f(int x):
	 *     debug "X = " + x
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * method f(int x):
	 * body:
	 *     const %2 = "X = "       : string
	 *     convert %0 = %0 any     : int
	 *     invoke %0 (%0) whiley/lang/Any:toString : string(any)
	 *     strappend %1 = %2, %0   : string
	 *     debug %1                : string
	 *     return
	 * </pre>
	 *
	 * <b>NOTE</b> This bytecode is not intended to form part of the program's
	 * operation. Rather, it is to facilitate debugging within functions (since
	 * they cannot have side-effects). Furthermore, if debugging is disabled,
	 * this bytecode is a nop.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Debug extends AbstractUnaryOp<Type.Strung> {

		private Debug(int operand) {
			super(Type.T_STRING, operand);
		}

		public int opcode() {
			return OPCODE_debug;
		}

		@Override
		public Code.Unit clone(int nOperand) {
			return Debug(nOperand);
		}

		public boolean equals(Object o) {
			return o instanceof Debug && super.equals(o);
		}

		public String toString() {
			return "debug %" + operand + " " + " : " + type;
		}
	}

	/**
	 * Marks the end of a loop block.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class LoopEnd extends Label {
		LoopEnd(String label) {
			super(label);
		}

		public LoopEnd relabel(Map<String, String> labels) {
			String nlabel = labels.get(label);
			if (nlabel == null) {
				return this;
			} else {
				return LoopEnd(nlabel);
			}
		}

		public int hashCode() {
			return label.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof LoopEnd) {
				LoopEnd e = (LoopEnd) o;
				return e.label.equals(label);
			}
			return false;
		}

		public String toString() {
			return "end " + label;
		}
	}

	/**
	 * An abstract class representing either an <code>assert</code> or
	 * <code>assume</code> bytecode block.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static abstract class AssertOrAssume extends Code.Unit {
		public final String target;


		private AssertOrAssume(String target) {
			this.target = target;
		}
	}
	/**
	 * Represents a block of bytecode instructions representing an assertion.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Assert extends AssertOrAssume {

		private Assert(String target) {
			super(target);
		}

		public int opcode() {
			return OPCODE_assertblock;
		}

		public String toString() {
			return "assert " + target;
		}
	}

	/**
	 * Represents a block of bytecode instructions representing an assumption.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Assume extends AssertOrAssume {

		private Assume(String target) {
			super(target);
		}

		public int opcode() {
			return OPCODE_assumeblock;
		}

		public String toString() {
			return "assume " + target;
		}
	}

	/**
	 * A bytecode that halts execution by raising a runtime fault. This bytecode
	 * signals that some has gone wrong, and is typically used to signal an
	 * assertion failure.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Fail extends Code.Unit {
		public final Constant.Strung message;

		private Fail(String message) {
			this.message = Constant.V_STRING(message);
		}

		@Override
		public int opcode() {
			return OPCODE_fail;
		}

		public String toString() {
			if(message == null) {
				return "fail";
			} else {
				return "fail \"" + message + "\"";
			}
		}
	}

	/**
	 * Reads a record value from an operand register, extracts the value of a
	 * given field and writes this to the target register. For example, the
	 * following Whiley code:
	 *
	 * <pre>
	 * type Point is {int x, int y}
	 *
	 * function f(Point p) => int:
	 *     return p.x + p.y
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f({int x,int y} p) => int:
	 * body:
	 *     fieldload %2 = %0 x    : {int x,int y}
	 *     fieldload %3 = %0 y    : {int x,int y}
	 *     add %1 = %2, %3        : int
	 *     return %1              : int
	 * </pre>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class FieldLoad extends
			AbstractUnaryAssignable<Type.EffectiveRecord> {
		public final String field;

		private FieldLoad(Type.EffectiveRecord type, int target, int operand,
				String field) {
			super(type, target, operand);
			if (field == null) {
				throw new IllegalArgumentException(
						"FieldLoad field argument cannot be null");
			}
			this.field = field;
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return FieldLoad(type(), nTarget, nOperands[0], field);
		}

		public int opcode() {
			return OPCODE_fieldload;
		}

		public int hashCode() {
			return super.hashCode() + field.hashCode();
		}

		public Type fieldType() {
			return type().fields().get(field);
		}

		public Type assignedType() {
			return type().fields().get(field);
		}

		public boolean equals(Object o) {
			if (o instanceof FieldLoad) {
				FieldLoad i = (FieldLoad) o;
				return super.equals(i) && field.equals(i.field);
			}
			return false;
		}

		public String toString() {
			return "fieldload %" + target() + " = %" + operand(0) + " " + field
					+ " : " + type();
		}
	}

	/**
	 * Branches unconditionally to the given label. This is typically used for
	 * if/else statements. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 *     if x >= 0:
	 *         x = 1
	 *     else:
	 *         x = -1
	 *     return x
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 * body:
	 *     const %1 = 0             : int
	 *     iflt %0, %1 goto blklab0 : int
	 *     const %0 = 1             : int
	 *     goto blklab1
	 * .blklab0
	 *     const %0 = 1             : int
	 *     neg %0 = % 0             : int
	 * .blklab1
	 *     return %0                : int
	 * </pre>
	 *
	 * Here, we see the <code>goto</code> bytecode being used to jump from the
	 * end of the true branch over the false branch.
	 *
	 * <p>
	 * <b>Note:</b> in WyIL bytecode, <i>such branches may only go forward</i>.
	 * Thus, a <code>goto</code> bytecode cannot be used to implement the
	 * back-edge of a loop. Rather, a loop block must be used for this purpose.
	 * </p>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Goto extends Code.Unit {
		public final String target;

		private Goto(String target) {
			this.target = target;
		}

		public int opcode() {
			return OPCODE_goto;
		}

		public Goto relabel(Map<String, String> labels) {
			String nlabel = labels.get(target);
			if (nlabel == null) {
				return this;
			} else {
				return Goto(nlabel);
			}
		}

		public int hashCode() {
			return target.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof Goto) {
				return target.equals(((Goto) o).target);
			}
			return false;
		}

		public String toString() {
			return "goto " + target;
		}
	}

	/**
	 * <p>
	 * Branches conditionally to the given label by reading the values from two
	 * operand registers and comparing them. The possible comparators are:
	 * </p>
	 * <ul>
	 * <li><i>equals (eq) and not-equals (ne)</i>. Both operands must have the
	 * given type.</li>
	 * <li><i>less-than (lt), less-than-or-equals (le), greater-than (gt) and
	 * great-than-or-equals (ge).</i> Both operands must have the given type,
	 * which additionally must by either <code>char</code>, <code>int</code> or
	 * <code>real</code>.</li>
	 * <li><i>element of (in).</i> The second operand must be a set whose
	 * element type is that of the first.</li>
	 * <li><i>subset (ss) and subset-equals (sse)</i>. Both operands must have
	 * the given type, which additionally must be a set.</li>
	 * </ul>
	 * For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 *     if x < y:
	 *         return -1
	 *     else if x > y:
	 *         return 1
	 *     else:
	 *         return 0
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 * body:
	 *     ifge %0, %1 goto blklab0 : int
	 *     const %2 = -1 : int
	 *     return %2 : int
	 * .blklab0
	 *     ifle %0, %1 goto blklab2 : int
	 *     const %2 = 1 : int
	 *     return %2 : int
	 * .blklab2
	 *     const %2 = 0 : int
	 *     return %2 : int
	 * </pre>
	 *
	 * <b>Note:</b> in WyIL bytecode, <i>such branches may only go forward</i>.
	 * Thus, an <code>ifgoto</code> bytecode cannot be used to implement the
	 * back-edge of a loop. Rather, a loop block must be used for this purpose.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class If extends AbstractBinaryOp<Type> {
		public final String target;
		public final Comparator op;

		private If(Type type, int leftOperand, int rightOperand, Comparator op,
				String target) {
			super(type, leftOperand, rightOperand);
			if (op == null) {
				throw new IllegalArgumentException(
						"IfGoto op argument cannot be null");
			}
			if (target == null) {
				throw new IllegalArgumentException(
						"IfGoto target argument cannot be null");
			}
			this.op = op;
			this.target = target;
		}

		public If relabel(Map<String, String> labels) {
			String nlabel = labels.get(target);
			if (nlabel == null) {
				return this;
			} else {
				return If(type, leftOperand, rightOperand, op, nlabel);
			}
		}

		public int opcode() {
			return OPCODE_ifeq + op.offset;
		}

		@Override
		public Code.Unit clone(int nLeftOperand, int nRightOperand) {
			return If(type, nLeftOperand, nRightOperand, op, target);
		}

		public int hashCode() {
			return super.hashCode() + op.hashCode() + target.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof If) {
				If ig = (If) o;
				return op == ig.op && target.equals(ig.target)
						&& super.equals(ig);
			}
			return false;
		}

		public String codeString() {
			return null;
		}

		public String toString() {
			return "if" + op + " %" + leftOperand + ", %" + rightOperand
					+ " goto " + target + " : " + type;
		}
	}

	/**
	 * Represents a comparison operator (e.g. '==','!=',etc) that is provided to
	 * a <code>IfGoto</code> bytecode.
	 *
	 * @author David J. Pearce
	 *
	 */
	public enum Comparator {
		EQ(0) {
			public String toString() {
				return "eq";
			}
		},
		NEQ(1) {
			public String toString() {
				return "ne";
			}
		},
		LT(2) {
			public String toString() {
				return "lt";
			}
		},
		LTEQ(3) {
			public String toString() {
				return "le";
			}
		},
		GT(4) {
			public String toString() {
				return "gt";
			}
		},
		GTEQ(5) {
			public String toString() {
				return "ge";
			}
		},
		IN(6) {
			public String toString() {
				return "in";
			}
		},
		SUBSET(7) {
			public String toString() {
				return "sb";
			}
		},
		SUBSETEQ(8) {
			public String toString() {
				return "sbe";
			}
		};
		public int offset;

		private Comparator(int offset) {
			this.offset = offset;
		}
	};

	/**
	 * Branches conditionally to the given label based on the result of a
	 * runtime type test against a value from the operand register. More
	 * specifically, it checks whether the value is a subtype of the type test.
	 * The operand register is automatically <i>retyped</i> as a result of the
	 * type test. On the true branch, its type is intersected with type test. On
	 * the false branch, its type is intersected with the <i>negation</i> of the
	 * type test. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int|[int] x) => int:
	 *     if x is [int]:
	 *         return |x|
	 *     else:
	 *         return x
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int|[int] x) => int:
	 * body:
	 *     ifis %0, [int] goto lab    : int|[int]
	 *     return %0                  : int
	 * .lab
	 *     lengthof %0 = %0           : [int]
	 *     return %0                  : int
	 * </pre>
	 *
	 * Here, we see that, on the false branch, register <code>%0</code> is
	 * automatically given type <code>int</code>, whilst on the true branch it
	 * is automatically given type <code>[int]</code>.
	 *
	 * <p>
	 * <b>Note:</b> in WyIL bytecode, <i>such branches may only go forward</i>.
	 * Thus, an <code>ifis</code> bytecode cannot be used to implement the
	 * back-edge of a loop. Rather, a loop block must be used for this purpose.
	 * </p>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class IfIs extends AbstractUnaryOp<Type> {
		public final String target;
		public final Type rightOperand;

		private IfIs(Type type, int leftOperand, Type rightOperand,
				String target) {
			super(type, leftOperand);
			if (rightOperand == null) {
				throw new IllegalArgumentException(
						"IfIs test argument cannot be null");
			}
			if (target == null) {
				throw new IllegalArgumentException(
						"IfIs target argument cannot be null");
			}
			this.target = target;
			this.rightOperand = rightOperand;
		}

		public int opcode() {
			return OPCODE_ifis;
		}

		public IfIs relabel(Map<String, String> labels) {
			String nlabel = labels.get(target);
			if (nlabel == null) {
				return this;
			} else {
				return IfIs(type, operand, rightOperand, nlabel);
			}
		}

		@Override
		public Code.Unit clone(int nOperand) {
			return IfIs(type, nOperand, rightOperand, target);
		}

		public int hashCode() {
			return type.hashCode() + +target.hashCode() + super.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof IfIs) {
				IfIs ig = (IfIs) o;
				return super.equals(o) && rightOperand.equals(ig.rightOperand)
						&& target.equals(ig.target);
			}
			return false;
		}

		public String toString() {
			return "ifis" + " %" + operand + ", " + rightOperand + " goto "
					+ target + " : " + type;
		}

	}

	/**
	 * Represents an indirect function call. For example, consider the
	 * following:
	 *
	 * <pre>
	 * function fun(function (int)=>int f, int x) => int:
	 *    return f(x)
	 * </pre>
	 *
	 * Here, the function call <code>f(x)</code> is indirect as the called
	 * function is determined by the variable <code>f</code>.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class IndirectInvoke extends
			AbstractNaryAssignable<Type.FunctionOrMethod> {

		/**
		 * Construct an indirect invocation bytecode which assigns to an
		 * optional target register the result from indirectly invoking a
		 * function in a given operand with a given set of parameter operands.
		 *
		 * @param type
		 * @param target Register (optional) to which result of invocation is assigned.
		 * @param operand Register holding function point through which indirect invocation is made.
		 * @param operands Registers holding parameters for the invoked function
		 */
		private IndirectInvoke(Type.FunctionOrMethod type, int target,
				int operand, int[] operands) {
			super(type, target, append(operand,operands));
		}

		/**
		 * Return register holding the indirect function/method reference.
		 *
		 * @return
		 */
		public int reference() {
			return operands()[0];
		}

		/**
		 * Return register holding the ith parameter for the invoked function.
		 *
		 * @param i
		 * @return
		 */
		public int parameter(int i) {
			return operands()[i + 1];
		}

		/**
		 * Return registers holding parameters for the invoked function.
		 *
		 * @param i
		 * @return
		 */
		public int[] parameters() {
			return Arrays.copyOfRange(operands(),1,operands().length);
		}

		public int opcode() {
			if (type() instanceof Type.Function) {
				if (target() != Codes.NULL_REG) {
					return OPCODE_indirectinvokefn;
				} else {
					return OPCODE_indirectinvokefnv;
				}
			} else {
				if (target() != Codes.NULL_REG) {
					return OPCODE_indirectinvokemd;
				} else {
					return OPCODE_indirectinvokemdv;
				}
			}
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return IndirectInvoke(type(), nTarget, nOperands[0],
					Arrays.copyOfRange(nOperands, 1, nOperands.length));
		}

		public boolean equals(Object o) {
			return o instanceof IndirectInvoke && super.equals(o);
		}

		public Type assignedType() {
			return type().ret();
		}

		public String toString() {
			if (target() != Codes.NULL_REG) {
				return "indirectinvoke " + target() + " = " + reference() + " "
						+ arrayToString(parameters()) + " : " + type();
			} else {
				return "indirectinvoke %" + reference() + " "
						+ arrayToString(parameters()) + " : " + type();
			}
		}
	}

	/**
	 * Read a boolean value from the operand register, inverts it and writes the
	 * result to the target register. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(bool x) => bool:
	 *     return !x
	 * </pre>
	 *
	 * can be translated into the following WyIL:
	 *
	 * <pre>
	 * function f(bool x) => bool:
	 * body:
	 *     not %0 = %0     : int
	 *     return %0       : int
	 * </pre>
	 *
	 * This simply reads the parameter <code>x</code> stored in register
	 * <code>%0</code>, inverts it and then returns the inverted value.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Not extends AbstractUnaryAssignable<Type.Bool> {

		private Not(int target, int operand) {
			super(Type.T_BOOL, target, operand);
		}

		public int opcode() {
			return OPCODE_not;
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return Not(nTarget, nOperands[0]);
		}

		public int hashCode() {
			return super.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof Not) {
				Not n = (Not) o;
				return super.equals(n);
			}
			return false;
		}

		public String toString() {
			return "not %" + target() + " = %" + operand(0) + " : " + type();
		}
	}

	/**
	 * Corresponds to a function or method call whose parameters are read from
	 * zero or more operand registers. If a return value is required, this is
	 * written to a target register afterwards. For example, the following
	 * Whiley code:
	 *
	 * <pre>
	 * function g(int x, int y, int z) => int:
	 *     return x * y * z
	 *
	 * function f(int x, int y) => int:
	 *     r = g(x,y,3)
	 *     return r + 1
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function g(int x, int y, int z) => int:
	 * body:
	 *     mul %3 = %0, %1   : int
	 *     mul %3 = %3, %2   : int
	 *     return %3         : int
	 *
	 * function f(int x, int y) => int:
	 * body:
	 *     const %2 = 3                    : int
	 *     invoke %2 = (%0, %1, %2) test:g   : int(int,int,int)
	 *     const %3 = 1                    : int
	 *     add %2 = (%2, %3)                : int
	 *     return %2                       : int
	 * </pre>
	 *
	 * Here, we see that arguments to the <code>invoke</code> bytecode are
	 * supplied in the order they are given in the function or method's
	 * declaration.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Invoke extends
			AbstractNaryAssignable<Type.FunctionOrMethod> {
		public final NameID name;

		private Invoke(Type.FunctionOrMethod type, int target, int[] operands,
				NameID name) {
			super(type, target, operands);
			this.name = name;
		}

		public int opcode() {
			if (type() instanceof Type.Function) {
				if (target() != Codes.NULL_REG) {
					return OPCODE_invokefn;
				} else {
					return OPCODE_invokefnv;
				}
			} else {
				if (target() != Codes.NULL_REG) {
					return OPCODE_invokemd;
				} else {
					return OPCODE_invokemdv;
				}
			}
		}

		public Type assignedType() {
			return type().ret();
		}

		public int hashCode() {
			return name.hashCode() + super.hashCode();
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return Invoke(type(), nTarget, nOperands, name);
		}

		public boolean equals(Object o) {
			if (o instanceof Invoke) {
				Invoke i = (Invoke) o;
				return name.equals(i.name) && super.equals(i);
			}
			return false;
		}

		public String toString() {
			if (target() != Codes.NULL_REG) {
				return "invoke %" + target() + " = " + arrayToString(operands())
						+ " " + name + " : " + type();
			} else {
				return "invoke %" + arrayToString(operands()) + " " + name
						+ " : " + type();
			}
		}
	}

	public static final class Lambda extends
			AbstractNaryAssignable<Type.FunctionOrMethod> {
		public final NameID name;

		private Lambda(Type.FunctionOrMethod type, int target, int[] operands,
				NameID name) {
			super(type, target, operands);
			this.name = name;
		}

		public int opcode() {
			if (type() instanceof Type.Function) {
				return OPCODE_lambdafn;
			} else {
				return OPCODE_lambdamd;
			}
		}

		public Type assignedType() {
			return type().ret();
		}

		public int hashCode() {
			return name.hashCode() + super.hashCode();
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return Lambda(type(), nTarget, nOperands, name);
		}

		public boolean equals(Object o) {
			if (o instanceof Lambda) {
				Lambda i = (Lambda) o;
				return name.equals(i.name) && super.equals(i);
			}
			return false;
		}

		public String toString() {
			return "lambda %" + target() + " = " + arrayToString(operands()) + " "
					+ name + " : " + type();
		}
	}

	/**
	 * Represents the labelled destination of a branch or loop statement.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Label extends Code.Unit {
		public final String label;

		private Label(String label) {
			this.label = label;
		}

		public int opcode() {
			return -1;
		}

		public Label relabel(Map<String, String> labels) {
			String nlabel = labels.get(label);
			if (nlabel == null) {
				return this;
			} else {
				return Label(nlabel);
			}
		}

		public int hashCode() {
			return label.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof Label) {
				return label.equals(((Label) o).label);
			}
			return false;
		}

		public String toString() {
			return "." + label;
		}
	}

	public enum ListOperatorKind {
		APPEND(0) {
			public String toString() {
				return "append";
			}
		},
		LEFT_APPEND(1) {
			public String toString() {
				return "appendl";
			}
		},
		RIGHT_APPEND(2) {
			public String toString() {
				return "appendr";
			}
		};
		public final int offset;

		private ListOperatorKind(int offset) {
			this.offset = offset;
		}
	}

	/**
	 * Reads the (effective) list values from two operand registers, performs an
	 * operation (e.g. append) on them and writes the result back to a target
	 * register. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f([int] xs, [int] ys) => [int]:
	 *    return xs ++ ys
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f([int] xs, [int] ys) => [int]:
	 * body:
	 *    append %2 = %0, %1   : [int]
	 *    return %2            : [int]
	 * </pre>
	 *
	 * This appends two the parameter lists together writting the new list into
	 * register <code>%2</code>.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class ListOperator extends
			AbstractBinaryAssignable<Type.EffectiveList> {
		public final ListOperatorKind kind;

		private ListOperator(Type.EffectiveList type, int target, int leftOperand,
				int rightOperand, ListOperatorKind operation) {
			super(type, target, leftOperand, rightOperand);
			if (operation == null) {
				throw new IllegalArgumentException(
						"ListAppend direction cannot be null");
			}
			this.kind = operation;
		}

		public int opcode() {
			return OPCODE_append + kind.offset;
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return ListOperator(type(), nTarget, nOperands[0], nOperands[1],
					kind);
		}

		public int hashCode() {
			return super.hashCode() + kind.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof ListOperator) {
				ListOperator setop = (ListOperator) o;
				return super.equals(setop) && kind.equals(setop.kind);
			}
			return false;
		}

		public String toString() {
			return kind + " %" + target() + " = %" + operand(0) + ", %"
					+ operand(1) + " : " + type();
		}
	}

	/**
	 * Reads an (effective) collection (i.e. a set, list or map) from the
	 * operand register, and writes its length into the target register. For
	 * example, the following Whiley code:
	 *
	 * <pre>
	 * function f([int] ls) => int:
	 *     return |ls|
	 * </pre>
	 *
	 * translates to the following WyIL code:
	 *
	 * <pre>
	 * function f([int] ls) => int:
	 * body:
	 *     lengthof %0 = %0   : [int]
	 *     return %0          : int
	 * </pre>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class LengthOf extends
			AbstractUnaryAssignable<Type.EffectiveCollection> {
		private LengthOf(Type.EffectiveCollection type, int target, int operand) {
			super(type, target, operand);
		}

		public int opcode() {
			return OPCODE_lengthof;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return LengthOf(type(), nTarget, nOperands[0]);
		}

		public Type assignedType() {
			return Type.T_INT;
		}

		public boolean equals(Object o) {
			if (o instanceof LengthOf) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "lengthof %" + target() + " = %" + operand(0) + " : " + type();
		}
	}

	/**
	 * Reads the (effective) list value from a source operand register, and the
	 * integer values from two index operand registers, computes the sublist and
	 * writes the result back to a target register.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class SubList extends
			AbstractNaryAssignable<Type.EffectiveList> {

		private SubList(Type.EffectiveList type, int target, int[] operands) {
			super(type, target, operands);
		}

		public int opcode() {
			return OPCODE_sublist;
		}

		@Override
		public final Code.Unit clone(int nTarget, int[] nOperands) {
			return SubList(type(), nTarget, nOperands);
		}

		public boolean equals(Object o) {
			return o instanceof SubList && super.equals(o);
		}

		public String toString() {
			return "sublist %" + target() + " = %" + operands()[0] + ", %"
					+ operands()[1] + ", %" + operands()[2] + " : " + type();
		}
	}

	/**
	 * Reads an effective list or map from the source (left) operand register,
	 * and a key value from the key (right) operand register and returns the
	 * value associated with that key. If the key does not exist, then a fault
	 * is raised. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f({int=>string} map, int key) => string:
	 *     return map[key]
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f({int->string} map, int key) => string:
	 * body:
	 *     assertky %1, %0 "invalid key"       : {int->string}
	 *     indexof %2 = %0, %1                 : {int->string}
	 *     return %2                          : string
	 * </pre>
	 *
	 * Here, we see the <code>assertky</code> bytecode is used to first check
	 * that the given key exists in <code>map</code>, otherwise a fault is
	 * raised.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class IndexOf extends
			AbstractBinaryAssignable<Type.EffectiveIndexible> {
		private IndexOf(Type.EffectiveIndexible type, int target,
				int sourceOperand, int keyOperand) {
			super(type, target, sourceOperand, keyOperand);
		}

		public int opcode() {
			return OPCODE_indexof;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return IndexOf(type(), nTarget, nOperands[0], nOperands[1]);
		}

		public Type assignedType() {
			return type().value();
		}

		public boolean equals(Object o) {
			if (o instanceof IndexOf) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "indexof %" + target() + " = %" + operand(0) + ", %"
					+ operand(1) + " : " + type();
		}
	}

	/**
	 * Moves the contents of a given operand register into a given target
	 * register. This is similar to an <code>assign</code> bytecode, except that
	 * the register's contents are <i>voided</i> afterwards. This guarantees
	 * that the register is no longer live, which is useful for determining the
	 * live ranges of registers in a function or method. For example, the
	 * following Whiley code:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 *     x = x + 1
	 *     return x
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 * body:
	 *     ifge %0, %1 goto blklab0  : int
	 *     move %0 = %1              : int
	 * .blklab0
	 *     return %0                 : int
	 * </pre>
	 *
	 * Here we see that when <code>x < y</code> the value of <code>y</code>
	 * (held in register <code>%1</code>) is <i>moved</i> into variable
	 * <code>x</code> (held in register <code>%0</code>). This is safe because
	 * register <code>%1</code> is no longer live at that point.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Move extends AbstractUnaryAssignable<Type> {

		private Move(Type type, int target, int operand) {
			super(type, target, operand);
		}

		public int opcode() {
			return OPCODE_move;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return Move(type(), nTarget, nOperands[0]);
		}

		public boolean equals(Object o) {
			if (o instanceof Move) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "move %" + target() + " = %" + operand(0) + " : " + type();
		}
	}

	/**
	 * Represents a block of code which loops continuously until e.g. a
	 * conditional branch is taken out of the block. For example:
	 *
	 * <pre>
	 * function f() => int:
	 *     r = 0
	 *     while r < 10:
	 *         r = r + 1
	 *     return r
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f() => int:
	 * body:
	 *     const %0 = 0             : int
	 *     loop (%0)
	 *         const %1 = 10        : int
	 *         ifge %0, %1 goto blklab0 : int
	 *         const %1 = 1         : int
	 *         add %0 = %0, %1      : int
	 * .blklab0
	 *     return %0                : int
	 * </pre>
	 *
	 * <p>
	 * Here, we see a loop which increments an accumulator register
	 * <code>%0</code> until it reaches <code>10</code>, and then exits the loop
	 * block.
	 * </p>
	 * <p>
	 * The <i>modified operands</i> of a loop bytecode (shown in brackets
	 * alongside the bytecode) indicate those operands which are modified at
	 * some point within the loop.
	 * </p>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Loop extends Code.Unit {
		public final String target;
		public final int[] modifiedOperands;

		private Loop(String target, int[] modifies) {
			this.target = target;
			this.modifiedOperands = modifies;
		}

		public int opcode() {
			return OPCODE_loop;
		}

		public Loop relabel(Map<String, String> labels) {
			String nlabel = labels.get(target);
			if (nlabel == null) {
				return this;
			} else {
				return Loop(nlabel, modifiedOperands);
			}
		}

		@Override
		public void registers(java.util.Set<Integer> registers) {
			for (int operand : modifiedOperands) {
				registers.add(operand);
			}
		}

		@Override
		public Code.Unit remap(Map<Integer, Integer> binding) {
			int[] nOperands = remapOperands(binding, modifiedOperands);
			if (nOperands != modifiedOperands) {
				return Loop(target, nOperands);
			} else {
				return this;
			}
		}

		public int hashCode() {
			return target.hashCode() + Arrays.hashCode(modifiedOperands);
		}

		public boolean equals(Object o) {
			if (o instanceof Loop) {
				Loop f = (Loop) o;
				return target.equals(f.target)
						&& Arrays.equals(modifiedOperands, f.modifiedOperands);
			}
			return false;
		}

		public String toString() {
			return "loop " + arrayToString(modifiedOperands);
		}
	}

	/**
	 * Pops a set, list or map from the stack and iterates over every element it
	 * contains. A register is identified to hold the current value being
	 * iterated over.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class ForAll extends Loop {
		public final int sourceOperand;
		public final int indexOperand;
		public final Type.EffectiveCollection type;

		private ForAll(Type.EffectiveCollection type, int sourceOperand,
				int indexOperand, int[] modifies, String target) {
			super(target, modifies);
			this.type = type;
			this.sourceOperand = sourceOperand;
			this.indexOperand = indexOperand;
		}

		public int opcode() {
			return OPCODE_forall;
		}

		public ForAll relabel(Map<String, String> labels) {
			String nlabel = labels.get(target);
			if (nlabel == null) {
				return this;
			} else {
				return ForAll(type, sourceOperand, indexOperand,
						modifiedOperands, nlabel);
			}
		}

		@Override
		public void registers(java.util.Set<Integer> registers) {
			registers.add(indexOperand);
			registers.add(sourceOperand);
			super.registers(registers);
		}

		@Override
		public Code.Unit remap(Map<Integer, Integer> binding) {
			int[] nModifiedOperands = remapOperands(binding, modifiedOperands);
			Integer nIndexOperand = binding.get(indexOperand);
			Integer nSourceOperand = binding.get(sourceOperand);
			if (nSourceOperand != null || nIndexOperand != null
					|| nModifiedOperands != modifiedOperands) {
				nSourceOperand = nSourceOperand != null ? nSourceOperand
						: sourceOperand;
				nIndexOperand = nIndexOperand != null ? nIndexOperand
						: indexOperand;

				return ForAll(type, nSourceOperand, nIndexOperand,
						nModifiedOperands, target);
			} else {
				return this;
			}
		}

		public int hashCode() {
			return super.hashCode() + sourceOperand + indexOperand
					+ Arrays.hashCode(modifiedOperands);
		}

		public boolean equals(Object o) {
			if (o instanceof ForAll) {
				ForAll f = (ForAll) o;
				return target.equals(f.target) && type.equals(f.type)
						&& sourceOperand == f.sourceOperand
						&& indexOperand == f.indexOperand
						&& Arrays.equals(modifiedOperands, f.modifiedOperands);
			}
			return false;
		}

		public String toString() {
			return "forall %" + indexOperand + " in %" + sourceOperand + " "
					+ arrayToString(modifiedOperands) + " : " + type;
		}
	}

	/**
	 * Represents a type which may appear on the left of an assignment
	 * expression. Lists, Dictionaries, Strings, Records and References are the
	 * only valid types for an lval.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static abstract class LVal<T> {
		protected T type;

		public LVal(T t) {
			this.type = t;
		}

		public T rawType() {
			return type;
		}
	}

	/**
	 * An LVal with map type.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class MapLVal extends LVal<Type.EffectiveMap> {
		public final int keyOperand;

		public MapLVal(Type.EffectiveMap t, int keyOperand) {
			super(t);
			this.keyOperand = keyOperand;
		}
	}

	/**
	 * An LVal with list type.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class ListLVal extends LVal<Type.EffectiveList> {
		public final int indexOperand;

		public ListLVal(Type.EffectiveList t, int indexOperand) {
			super(t);
			this.indexOperand = indexOperand;
		}
	}

	/**
	 * An LVal with list type.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class ReferenceLVal extends LVal<Type.Reference> {
		public ReferenceLVal(Type.Reference t) {
			super(t);
		}
	}

	/**
	 * An LVal with string type.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class StringLVal extends LVal<Type.EffectiveIndexible> {
		public final int indexOperand;

		public StringLVal(int indexOperand) {
			super(Type.T_STRING);
			this.indexOperand = indexOperand;
		}
	}

	/**
	 * An LVal with record type.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class RecordLVal extends LVal<Type.EffectiveRecord> {
		public final String field;

		public RecordLVal(Type.EffectiveRecord t, String field) {
			super(t);
			this.field = field;
			if (!t.fields().containsKey(field)) {
				throw new IllegalArgumentException("invalid Record Type");
			}
		}
	}

	private static final class UpdateIterator implements Iterator<LVal> {
		private final ArrayList<String> fields;
		private final int[] operands;
		private Type iter;
		private int fieldIndex;
		private int operandIndex;
		private int index;

		public UpdateIterator(Type type, int level, int[] operands,
				ArrayList<String> fields) {
			this.fields = fields;
			this.iter = type;
			this.index = level;
			this.operands = operands;
		}

		public LVal next() {
			Type raw = iter;
			index--;
			if (Type.isSubtype(Type.T_STRING, iter)) {
				iter = Type.T_CHAR;
				return new StringLVal(operands[operandIndex++]);
			} else if (Type.isSubtype(Type.Reference(Type.T_ANY), iter)) {
				Type.Reference proc = Type.effectiveReference(iter);
				iter = proc.element();
				return new ReferenceLVal(proc);
			} else if (iter instanceof Type.EffectiveList) {
				Type.EffectiveList list = (Type.EffectiveList) iter;
				iter = list.element();
				return new ListLVal(list, operands[operandIndex++]);
			} else if (iter instanceof Type.EffectiveMap) {
				Type.EffectiveMap dict = (Type.EffectiveMap) iter;
				iter = dict.value();
				return new MapLVal(dict, operands[operandIndex++]);
			} else if (iter instanceof Type.EffectiveRecord) {
				Type.EffectiveRecord rec = (Type.EffectiveRecord) iter;
				String field = fields.get(fieldIndex++);
				iter = rec.fields().get(field);
				return new RecordLVal(rec, field);
			} else {
				throw new IllegalArgumentException(
						"Invalid type for Update");
			}
		}

		public boolean hasNext() {
			return index > 0;
		}

		public void remove() {
			throw new UnsupportedOperationException(
					"UpdateIterator is unmodifiable");
		}
	}

	/**
	 * <p>
	 * Pops a compound structure, zero or more indices and a value from the
	 * stack and updates the compound structure with the given value. Valid
	 * compound structures are lists, dictionaries, strings, records and
	 * references.
	 * </p>
	 * <p>
	 * Ideally, this operation is done in-place, meaning the operation is
	 * constant time. However, to support Whiley's value semantics this bytecode
	 * may require (in some cases) a clone of the underlying data-structure.
	 * Thus, the worst-case runtime of this operation is linear in the size of
	 * the compound structure.
	 * </p>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Update extends AbstractNaryAssignable<Type>
			implements Iterable<LVal> {
		public final Type afterType;
		public final ArrayList<String> fields;

		/**
		 * Construct an Update bytecode which assigns to a given operand to a
		 * set of target registers. For indirect map/list updates, an additional
		 * set of operands is used to generate the appropriate keys. For field
		 * assignments, a set of fields is provided.
		 *
		 * @param beforeType
		 * @param target
		 *            Register being assigned
		 * @param operands
		 *            Registers used for keys on left-hand side in map/list
		 *            updates
		 * @param operand
		 *            Register on right-hand side whose value is assigned
		 * @param afterType
		 * @param fields
		 *            Fields for record updates
		 */
		private Update(Type beforeType, int target, int[] operands,
				int operand, Type afterType, Collection<String> fields) {
			super(beforeType, target, append(operands,operand));
			if (fields == null) {
				throw new IllegalArgumentException(
						"FieldStore fields argument cannot be null");
			}
			this.afterType = afterType;
			this.fields = new ArrayList<String>(fields);
		}

		// Helper used for clone()
		private Update(Type beforeType, int target, int[] operands,
				Type afterType, Collection<String> fields) {
			super(beforeType, target, operands);
			if (fields == null) {
				throw new IllegalArgumentException(
						"FieldStore fields argument cannot be null");
			}
			this.afterType = afterType;
			this.fields = new ArrayList<String>(fields);
		}

		public int opcode() {
			return OPCODE_update;
		}

		/**
		 * Returns register from which assigned value is read. This is also
		 * known as the "right-hand side".
		 *
		 * @return
		 */
		public int result() {
			return operands()[operands().length-1];
		}

		/**
		 * Get the given key register (in order of appearance from the left)
		 * used in a map or list update.
		 *
		 * @param index
		 * @return
		 */
		public int key(int index) {
			return operands()[index];
		}

		/**
		 * Return the registers used to hold key values for map or list updates.
		 *
		 * @return
		 */
		public int[] keys() {
			return Arrays.copyOf(operands(),operands().length-1);
		}

		public int level() {
			int base = -1; // because last operand is rhs
			if (type() instanceof Type.Reference) {
				base++;
			}
			return base + fields.size() + operands().length;
		}

		public Iterator<LVal> iterator() {
			return new UpdateIterator(afterType, level(), keys(), fields);
		}

		public Type assignedType() {
			return afterType;
		}

		/**
		 * Extract the type for the right-hand side of this assignment.
		 *
		 * @return
		 */
		public Type rhs() {
			Type iter = afterType;

			int fieldIndex = 0;
			for (int i = 0; i != level(); ++i) {
				if (Type.isSubtype(Type.T_STRING, iter)) {
					iter = Type.T_CHAR;
				} else if (Type.isSubtype(Type.Reference(Type.T_ANY), iter)) {
					Type.Reference proc = Type.effectiveReference(iter);
					iter = proc.element();
				} else if (iter instanceof Type.EffectiveList) {
					Type.EffectiveList list = (Type.EffectiveList) iter;
					iter = list.element();
				} else if (iter instanceof Type.EffectiveMap) {
					Type.EffectiveMap dict = (Type.EffectiveMap) iter;
					iter = dict.value();
				} else if (iter instanceof Type.EffectiveRecord) {
					Type.EffectiveRecord rec = (Type.EffectiveRecord) iter;
					String field = fields.get(fieldIndex++);
					iter = rec.fields().get(field);
				} else {
					throw new IllegalArgumentException(
							"Invalid type for Update");
				}
			}
			return iter;
		}

		@Override
		public final Code.Unit clone(int nTarget, int[] nOperands) {
			return Update(type(), nTarget,
					Arrays.copyOf(nOperands, nOperands.length - 1),
					nOperands[nOperands.length - 1], afterType, fields);
		}

		public boolean equals(Object o) {
			if (o instanceof Update) {
				Update i = (Update) o;
				return super.equals(o) && afterType.equals(i.afterType)
						&& fields.equals(i.fields);
			}
			return false;
		}

		public String toString() {
			String r = "%" + target();
			for (LVal lv : this) {
				if (lv instanceof ListLVal) {
					ListLVal l = (ListLVal) lv;
					r = r + "[%" + l.indexOperand + "]";
				} else if (lv instanceof StringLVal) {
					StringLVal l = (StringLVal) lv;
					r = r + "[%" + l.indexOperand + "]";
				} else if (lv instanceof MapLVal) {
					MapLVal l = (MapLVal) lv;
					r = r + "[%" + l.keyOperand + "]";
				} else if (lv instanceof RecordLVal) {
					RecordLVal l = (RecordLVal) lv;
					r = r + "." + l.field;
				} else {
					ReferenceLVal l = (ReferenceLVal) lv;
					r = "(*" + r + ")";
				}
			}
			return "update " + r + " = %" + result() + " : " + type() + " -> "
					+ afterType;
		}
	}

	/**
	 * Constructs a map value from zero or more key-value pairs on the stack.
	 * For each pair, the key must occur directly before the value on the stack.
	 * For example, consider the following Whiley function <code>f()</code>:
	 *
	 * <pre>
	 * function f() => {int=>string}:
	 *     return {1=>"Hello",2=>"World"}
	 * </pre>
	 *
	 * This could be compiled into the following WyIL code using this bytecode:
	 *
	 * <pre>
	 * function f() => {int->string}:
	 * body:
	 *   const %1 = 1                   : int
	 *   const %2 = "Hello"             : string
	 *   const %3 = 2                   : int
	 *   const %4 = "World"             : string
	 *   newmap %0 = (%1, %2, %3, %4)   : {int=>string}
	 *   return %0                      : {int=>string}
	 * </pre>
	 *
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class NewMap extends AbstractNaryAssignable<Type.Map> {

		private NewMap(Type.Map type, int target, int[] operands) {
			super(type, target, operands);
		}

		public int opcode() {
			return OPCODE_newmap;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return NewMap(type(), nTarget, nOperands);
		}

		public boolean equals(Object o) {
			if (o instanceof NewMap) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "newmap %" + target() + " = " + arrayToString(operands())
					+ " : " + type();
		}
	}

	/**
	 * Constructs a new record value from the values of zero or more operand
	 * register, each of which is associated with a field name. The new record
	 * value is then written into the target register. For example, the
	 * following Whiley code:
	 *
	 * <pre>
	 * type Point is {real x, real y}
	 *
	 * function f(real x, real y) => Point:
	 *     return {x: x, y: x}
	 * </pre>
	 *
	 * can be translated into the following WyIL:
	 *
	 * <pre>
	 * function f(real x, real y) => Point:
	 * body:
	 *     assign %3 = %0         : real
	 *     assign %4 = %0         : real
	 *     newrecord %2 (%3, %4)  : {real x,real y}
	 *     return %2              : {real x,real y}
	 * </pre>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class NewRecord extends
			AbstractNaryAssignable<Type.Record> {
		private NewRecord(Type.Record type, int target, int[] operands) {
			super(type, target, operands);
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return NewRecord(type(), nTarget, nOperands);
		}

		public int opcode() {
			return OPCODE_newrecord;
		}

		public boolean equals(Object o) {
			if (o instanceof NewRecord) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "newrecord %" + target() + " = " + arrayToString(operands())
					+ " : " + type();
		}
	}

	/**
	 * Constructs a new tuple value from the values given by zero or more
	 * operand registers. The new tuple is then written into the target
	 * register. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x, int y) => (int,int):
	 *     return x,y
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x, int y) => (int,int):
	 * body:
	 *     assign %3 = %0          : int
	 *     assign %4 = %1          : int
	 *     newtuple %2 = (%3, %4)  : (int,int)
	 *     return %2               : (int,int)
	 * </pre>
	 *
	 * This writes the tuple value generated from <code>(x,y)</code> into
	 * register <code>%2</code> and returns it.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class NewTuple extends
			AbstractNaryAssignable<Type.Tuple> {

		private NewTuple(Type.Tuple type, int target, int[] operands) {
			super(type, target, operands);
		}

		public int opcode() {
			return OPCODE_newtuple;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return NewTuple(type(), nTarget, nOperands);
		}

		public boolean equals(Object o) {
			if (o instanceof NewTuple) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "newtuple %" + target() + " = " + arrayToString(operands())
					+ " : " + type();
		}
	}

	/**
	 * Constructs a new set value from the values given by zero or more operand
	 * registers. The new set is then written into the target register. For
	 * example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x, int y, int z) => {int}:
	 *     return {x,y,z}
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x, int y, int z) => {int}:
	 * body:
	 *    assign %4 = %0             : int
	 *    assign %5 = %1             : int
	 *    assign %6 = %2             : int
	 *    newset %3 = (%4, %5, %6)   : [int]
	 *    return %3                  : [int]
	 * </pre>
	 *
	 * Writes the set value given by <code>{x,y,z}</code> into register
	 * <code>%3</code> and returns it.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class NewSet extends AbstractNaryAssignable<Type.Set> {

		private NewSet(Type.Set type, int target, int[] operands) {
			super(type, target, operands);
		}

		public int opcode() {
			return OPCODE_newset;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return NewSet(type(), nTarget, nOperands);
		}

		public boolean equals(Object o) {
			if (o instanceof NewSet) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "newset %" + target() + " = " + arrayToString(operands())
					+ " : " + type();
		}
	}

	/**
	 * Constructs a new list value from the values given by zero or more operand
	 * registers. The new list is then written into the target register. For
	 * example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x, int y, int z) => [int]:
	 *     return [x,y,z]
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x, int y, int z) => [int]:
	 * body:
	 *    assign %4 = %0             : int
	 *    assign %5 = %1             : int
	 *    assign %6 = %2             : int
	 *    newlist %3 = (%4, %5, %6)  : [int]
	 *    return %3                  : [int]
	 * </pre>
	 *
	 * Writes the list value given by <code>[x,y,z]</code> into register
	 * <code>%3</code> and returns it.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class NewList extends AbstractNaryAssignable<Type.List> {

		private NewList(Type.List type, int target, int[] operands) {
			super(type, target, operands);
		}

		public int opcode() {
			return OPCODE_newlist;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return NewList(type(), nTarget, nOperands);
		}

		public boolean equals(Object o) {
			if (o instanceof NewList) {
				return super.equals(operands());
			}
			return false;
		}

		public String toString() {
			return "newlist %" + target() + " = " + arrayToString(operands())
					+ " : " + type();
		}
	}

	/**
	 * Represents a no-operation bytecode which, as the name suggests, does
	 * nothing.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Nop extends Code.Unit {
		private Nop() {
		}

		@Override
		public int opcode() {
			return OPCODE_nop;
		}

		public String toString() {
			return "nop";
		}
	}

	/**
	 * Returns from the enclosing function or method, possibly returning a
	 * value. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 *     return x + y
	 * </pre>
	 *
	 * can be translated into the following WyIL:
	 *
	 * <pre>
	 * function f(int x, int y) => int:
	 * body:
	 *     assign %3 = %0    : int
	 *     assign %4 = %1    : int
	 *     add %2 = % 3, %4  : int
	 *     return %2         : int
	 * </pre>
	 *
	 * Here, the
	 * <code>return<code> bytecode returns the value of its operand register.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Return extends AbstractUnaryOp<Type> {

		private Return(Type type, int operand) {
			super(type, operand);
			if (type == Type.T_VOID && operand != Codes.NULL_REG) {
				throw new IllegalArgumentException(
						"Return with void type cannot have target register.");
			} else if (type != Type.T_VOID && operand == Codes.NULL_REG) {
				throw new IllegalArgumentException(
						"Return with non-void type must have target register.");
			}
		}

		@Override
		public int opcode() {
			if (type == Type.T_VOID) {
				return OPCODE_returnv;
			} else {
				return OPCODE_return;
			}
		}

		public Code.Unit clone(int nOperand) {
			return new Return(type, nOperand);
		}

		public boolean equals(Object o) {
			if (o instanceof Return) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			if (operand != Codes.NULL_REG) {
				return "return %" + operand + " : " + type;
			} else {
				return "return";
			}
		}
	}

	public enum SetOperatorKind {
		UNION(0) {
			public String toString() {
				return "union";
			}
		},
		LEFT_UNION(1) {
			public String toString() {
				return "unionl";
			}
		},
		RIGHT_UNION(2) {
			public String toString() {
				return "unionl";
			}
		},
		INTERSECTION(3) {
			public String toString() {
				return "intersect";
			}
		},
		LEFT_INTERSECTION(4) {
			public String toString() {
				return "intersectl";
			}
		},
		RIGHT_INTERSECTION(5) {
			public String toString() {
				return "intersectr";
			}
		},
		DIFFERENCE(6) {
			public String toString() {
				return "diff";
			}
		},
		LEFT_DIFFERENCE(7) {
			public String toString() {
				return "diffl";
			}
		};
		public final int offset;

		private SetOperatorKind(int offset) {
			this.offset = offset;
		}
	}

	/**
	 * <p>
	 * A binary operation which reads two set values from the operand registers,
	 * performs an operation on them and writes the result to the target
	 * register. The binary set operators are:
	 * </p>
	 * <ul>
	 * <li><i>union, intersection, difference</i>. Both operands must be have
	 * the given (effective) set type. same type is produced.</li>
	 * <li><i>left union, left intersection, left difference</i>. The left
	 * operand must have the given (effective) set type, whilst the right
	 * operand has the given (effective) set element type.</li>
	 * <li><i>right union, right intersection</i>. The right operand must have
	 * the given (effective) set type, whilst the left operand has the given
	 * (effective) set element type.</li>
	 * </ul>
	 * For example, the following Whiley code:
	 *
	 * <pre>
	 * function f({int} xs, {int} ys) => {int}:
	 *     return xs + ys // set union
	 *
	 * function g(int x, {int} ys) => {int}:
	 *     return {x} & ys // set intersection
	 *
	 * function h({int} xs, int y) => {int}:
	 *     return xs - {y} // set difference
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f({int} xs, {int} ys) => {int}:
	 * body:
	 *     union %2 = %0, %1  : {int}
	 *     return %2          : {int}
	 *
	 * function g({int} xs, {int} ys) => {int}:
	 * body:
	 *     rintersect %2 = %0, %1  : {int}
	 *     return %2               : {int}
	 *
	 * function h({int} xs, {int} ys) => {int}:
	 * body:
	 *     ldiff %2 = %0, %1    : {int}
	 *     return %2            : {int}
	 * </pre>
	 *
	 * Here, we see that the purpose of the <i>left-</i> and <i>right-</i>
	 * operations is to avoid creating a temporary set in the common case of a
	 * single element set on one side. This is largely an optimisation and it is
	 * expected that the front-end of the compiler will spots such situations
	 * and compile them down appropriately.
	 *
	 * @author David J. Pearce
	 */
	public static final class SetOperator extends
			AbstractBinaryAssignable<Type.EffectiveSet> {
		public final SetOperatorKind kind;

		private SetOperator(Type.EffectiveSet type, int target, int leftOperand,
				int rightOperand, SetOperatorKind operation) {
			super(type, target, leftOperand, rightOperand);
			if (operation == null) {
				throw new IllegalArgumentException(
						"SetOp operation cannot be null");
			}
			this.kind = operation;
		}

		@Override
		public int opcode() {
			return OPCODE_union + kind.offset;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return SetOperator(type(), nTarget, nOperands[0], nOperands[1],
					kind);
		}

		public int hashCode() {
			return kind.hashCode() + super.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof SetOperator) {
				SetOperator setop = (SetOperator) o;
				return kind.equals(setop.kind) && super.equals(o);
			}
			return false;
		}

		public String toString() {
			return kind + " %" + target() + " = %" + operand(0) + ", %"
					+ operand(1) + " : " + type();
		}
	}

	public enum StringOperatorKind {
		APPEND(0) {
			public String toString() {
				return "sappend";
			}
		},
		LEFT_APPEND(1) {
			public String toString() {
				return "sappendl";
			}
		},
		RIGHT_APPEND(2) {
			public String toString() {
				return "sappendr";
			}
		};
		public final int offset;

		private StringOperatorKind(int offset) {
			this.offset = offset;
		}
	}

	/**
	 * <p>
	 * A binary operation which reads two string values from the operand
	 * registers, performs an operation (append) on them and writes the result
	 * to the target register. The binary set operators are:
	 * </p>
	 * <ul>
	 * <li><i>append</i>. Both operands must be have string type.</li>
	 * <li><i>left append</i>. The left operand must have string type, whilst
	 * the right operand has char type.</li>
	 * <li><i>right append</i>. The right operand must have string type, whilst
	 * the left operand has char type.</li>
	 * </ul>
	 * For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(string xs, string ys) => string:
	 *     return xs ++ ys
	 *
	 * function g(string xs, char y) => string:
	 *     return xs ++ y
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(string xs, string ys) => string:
	 * body:
	 *     strappend %2 = %0, %2    : string
	 *     return %2                : string
	 *
	 * function g(string xs, char y) => string:
	 * body:
	 *     strappend_l %2 = %0, %1  : string
	 *     return %2                : string
	 * </pre>
	 *
	 * Here, we see that the purpose of the <i>left-</i> and <i>right-</i>
	 * operations is to avoid creating a temporary string in the common case of
	 * a single char being appended.
	 *
	 * @author David J. Pearce
	 */
	public static final class StringOperator extends
			AbstractBinaryAssignable<Type.Strung> {
		public final StringOperatorKind kind;

		private StringOperator(int target, int leftOperand, int rightOperand,
				StringOperatorKind operation) {
			super(Type.T_STRING, target, leftOperand, rightOperand);
			if (operation == null) {
				throw new IllegalArgumentException(
						"StringBinOp operation cannot be null");
			}
			this.kind = operation;
		}

		@Override
		public int opcode() {
			return OPCODE_sappend + kind.offset;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return StringOperator(nTarget, nOperands[0], nOperands[1], kind);
		}

		public boolean equals(Object o) {
			if (o instanceof StringOperator) {
				StringOperator setop = (StringOperator) o;
				return kind.equals(setop.kind) && super.equals(o);
			}
			return false;
		}

		public String toString() {
			return kind + " %" + target() + " = %" + operand(0) + ", %"
					+ operand(1) + " : " + type();
		}
	}

	/**
	 * Reads the string value from a source operand register, and the integer
	 * values from two index operand registers, computes the substring and
	 * writes the result back to a target register.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class SubString extends AbstractNaryAssignable {

		private SubString(int target, int[] operands) {
			super(Type.T_STRING, target, operands);
		}

		@Override
		public int opcode() {
			return OPCODE_substring;
		}

		@Override
		public final Code.Unit clone(int nTarget, int[] nOperands) {
			return SubString(nTarget, nOperands);
		}

		public boolean equals(Object o) {
			return o instanceof SubString && super.equals(o);
		}

		public String toString() {
			return "substr %" + target() + " = %" + operands()[0] + ", %"
					+ operands()[1] + ", %" + operands()[2] + " : " + type();
		}
	}

	/**
	 * Performs a multi-way branch based on the value contained in the operand
	 * register. A <i>dispatch table</i> is provided which maps individual
	 * matched values to their destination labels. For example, the following
	 * Whiley code:
	 *
	 * <pre>
	 * function f(int x) => string:
	 *     switch x:
	 *         case 1:
	 *             return "ONE"
	 *         case 2:
	 *             return "TWO"
	 *         default:
	 *             return "OTHER"
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x) => string:
	 * body:
	 *     switch %0 1->blklab1, 2->blklab2, *->blklab3
	 * .blklab1
	 *     const %1 = "ONE" : string
	 *     return %1 : string
	 * .blklab2
	 *     const %1 = "TWO" : string
	 *     return %1 : string
	 * .blklab3
	 *     const %1 = "OTHER" : string
	 *     return %1 : string
	 * </pre>
	 *
	 * Here, we see how e.g. value <code>1</code> is mapped to the label
	 * <code>blklab1</code>. Thus, if the operand register <code>%0</code>
	 * contains value <code>1</code>, then control will be transferred to that
	 * label. The final mapping <code>*->blklab3</code> covers the default case
	 * where the value in the operand is not otherwise matched.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Switch extends AbstractUnaryOp<Type> {
		public final ArrayList<Pair<Constant, String>> branches;
		public final String defaultTarget;

		Switch(Type type, int operand, String defaultTarget,
				Collection<Pair<Constant, String>> branches) {
			super(type, operand);
			this.branches = new ArrayList<Pair<Constant, String>>(branches);
			this.defaultTarget = defaultTarget;
		}

		@Override
		public int opcode() {
			return OPCODE_switch;
		}

		public Switch relabel(Map<String, String> labels) {
			ArrayList<Pair<Constant, String>> nbranches = new ArrayList();
			for (Pair<Constant, String> p : branches) {
				String nlabel = labels.get(p.second());
				if (nlabel == null) {
					nbranches.add(p);
				} else {
					nbranches.add(new Pair(p.first(), nlabel));
				}
			}

			String nlabel = labels.get(defaultTarget);
			if (nlabel == null) {
				return Switch(type, operand, defaultTarget, nbranches);
			} else {
				return Switch(type, operand, nlabel, nbranches);
			}
		}

		public int hashCode() {
			return type.hashCode() + operand + defaultTarget.hashCode()
					+ branches.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof Switch) {
				Switch ig = (Switch) o;
				return operand == ig.operand
						&& defaultTarget.equals(ig.defaultTarget)
						&& branches.equals(ig.branches) && type.equals(ig.type);
			}
			return false;
		}

		public String toString() {
			String table = "";
			boolean firstTime = true;
			for (Pair<Constant, String> p : branches) {
				if (!firstTime) {
					table += ", ";
				}
				firstTime = false;
				table += p.first() + "->" + p.second();
			}
			table += ", *->" + defaultTarget;
			return "switch %" + operand + " " + table;
		}

		@Override
		public Code.Unit clone(int nOperand) {
			return new Switch(type, nOperand, defaultTarget, branches);
		}

	}

	/**
	 * Throws an exception containing the value in the given operand register.
	 * For example, the following Whiley Code:
	 *
	 * <pre>
	 * function f(int x) => int
	 * throws string:
	 *     if x < 0:
	 *         throw "ERROR"
	 *     else:
	 *         return 1
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x) => int
	 * throws:
	 * 	   string
	 * body:
	 *     const %1 = 0 : int
	 *     ifge %0, %1 goto blklab0 : int
	 *     const %1 = "ERROR" : string
	 *     throw %1 : string
	 * .blklab0
	 *     const %1 = 1 : int
	 *     return %1 : int
	 * </pre>
	 *
	 * Here, we see an exception containing a <code>string</code> value will be
	 * thrown when the parameter <code>x</code> is negative.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Throw extends AbstractUnaryOp<Type> {
		private Throw(Type type, int operand) {
			super(type, operand);
		}

		@Override
		public int opcode() {
			return OPCODE_throw;
		}

		@Override
		public Code.Unit clone(int nOperand) {
			return Throw(type, nOperand);
		}

		public boolean equals(Object o) {
			if (o instanceof Throw) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "throw %" + operand + " : " + type;
		}
	}

	/**
	 * Represents a try-catch block within which specified exceptions will
	 * caught and processed within a handler. For example, the following Whiley
	 * code:
	 *
	 * <pre>
	 * function f(int x) => int
	 * throws Error:
	 *     ...
	 *
	 * function g(int x) => int:
	 *     try:
	 *         x = f(x)
	 *     catch(Error e):
	 *         return 0
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 * throws:
	 *     Error
	 * body:
	 *     ...
	 *
	 * function g(int x) => int:
	 * body:
	 *     trycatch Error -> lab2
	 *        assign %3 = %0           : int
	 *        invoke %0 = (%3) test:f  : int(int) throws {string msg}
	 *     return
	 * .lab2
	 *     const %3 = 0                : int
	 *     return %3                   : int
	 * </pre>
	 *
	 * Here, we see that within the try-catch block control is transferred to
	 * <code>lab2</code> if an exception of type <code>Error</code> is thrown.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class TryCatch extends Code.Unit {
		public final int operand;
		public final String target;
		public final ArrayList<Pair<Type, String>> catches;

		TryCatch(int operand, String label,
				Collection<Pair<Type, String>> catches) {
			this.operand = operand;
			this.catches = new ArrayList<Pair<Type, String>>(catches);
			this.target = label;
		}

		@Override
		public int opcode() {
			return OPCODE_trycatch;
		}

		@Override
		public void registers(java.util.Set<Integer> registers) {
			registers.add(operand);
		}

		@Override
		public Code.Unit remap(Map<Integer, Integer> binding) {
			Integer nOperand = binding.get(operand);
			if (nOperand != null) {
				return TryCatch(nOperand, target, catches);
			}
			return this;
		}

		public TryCatch relabel(Map<String, String> labels) {
			ArrayList<Pair<Type, String>> nbranches = new ArrayList();
			for (Pair<Type, String> p : catches) {
				String nlabel = labels.get(p.second());
				if (nlabel == null) {
					nbranches.add(p);
				} else {
					nbranches.add(new Pair(p.first(), nlabel));
				}
			}

			String ntarget = labels.get(target);
			if (ntarget != null) {
				return TryCatch(operand, ntarget, nbranches);
			} else {
				return TryCatch(operand, target, nbranches);
			}
		}

		public int hashCode() {
			return operand + target.hashCode() + catches.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof TryCatch) {
				TryCatch ig = (TryCatch) o;
				return operand == ig.operand && target.equals(ig.target)
						&& catches.equals(ig.catches);
			}
			return false;
		}

		public String toString() {
			String table = "";
			boolean firstTime = true;
			for (Pair<Type, String> p : catches) {
				if (!firstTime) {
					table += ", ";
				}
				firstTime = false;
				table += p.first() + "->" + p.second();
			}
			return "trycatch " + table;
		}
	}

	/**
	 * Marks the end of a try-catch block.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class TryEnd extends Label {
		TryEnd(String label) {
			super(label);
		}

		public TryEnd relabel(Map<String, String> labels) {
			String nlabel = labels.get(label);
			if (nlabel == null) {
				return this;
			} else {
				return TryEnd(nlabel);
			}
		}

		public int hashCode() {
			return label.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof TryEnd) {
				TryEnd e = (TryEnd) o;
				return e.label.equals(label);
			}
			return false;
		}

		public String toString() {
			return "tryend " + label;
		}
	}

	/**
	 * Corresponds to a bitwise inversion operation, which reads a byte value
	 * from the operand register, inverts it and writes the result to the target
	 * resgister. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(byte x) => byte:
	 *    return ~x
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(byte x) => byte:
	 * body:
	 *     invert %0 = %0   : byte
	 *     return %0        : byte
	 * </pre>
	 *
	 * Here, the expression <code>~x</code> generates an <code>invert</code>
	 * bytecode.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Invert extends AbstractUnaryAssignable<Type> {

		private Invert(Type type, int target, int operand) {
			super(type, target, operand);
		}

		@Override
		public int opcode() {
			return OPCODE_invert;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return Invert(type(), nTarget, nOperands[0]);
		}

		public boolean equals(Object o) {
			if (o instanceof Invert) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "invert %" + target() + " = %" + operand(0) + " : " + type();
		}
	}

	/**
	 * Instantiate a new object from the value in a given operand register, and
	 * write the result (a reference to that object) to a given target register.
	 * For example, the following Whiley code:
	 *
	 * <pre>
	 * type PointObj as &{real x, real y}
	 *
	 * method f(real x, real y) => PointObj:
	 *     return new {x: x, y: y}
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * method f(int x, int y) => &{real x,real y}:
	 * body:
	 *     newrecord %2 = (%0, %1)  : {real x,real y}
	 *     newobject %2 = %2        : ref {real x,real y}
	 *     return %2                : ref {real x,real y}
	 * </pre>
	 *
	 * <b>NOTE:</b> objects are unlike other data types in WyIL, in that they
	 * represent mutable state allocated on a heap. Thus, changes to an object
	 * within a method are visible to those outside of the method.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class NewObject extends
			AbstractUnaryAssignable<Type.Reference> {

		private NewObject(Type.Reference type, int target, int operand) {
			super(type, target, operand);
		}

		@Override
		public int opcode() {
			return OPCODE_newobject;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return NewObject(type(), nTarget, nOperands[0]);
		}

		public boolean equals(Object o) {
			if (o instanceof NewObject) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "newobject %" + target() + " = %" + operand(0) + " : " + type();
		}
	}

	/**
	 * Read a tuple value from the operand register, extract the value it
	 * contains at a given index and write that to the target register. For
	 * example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int,int tup) => int:
	 *     return tup[0]
	 * </pre>
	 *
	 * can be translated into the following WyIL code:
	 *
	 * <pre>
	 * function f(int,int tup) => int:
	 * body:
	 *     tupleload %0 = %0 0  : int,int
	 *     return %0            : int
	 * </pre>
	 *
	 * This simply reads the parameter <code>x</code> stored in register
	 * <code>%0</code>, and returns the value stored at index <code>0</code>.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class TupleLoad extends
			AbstractUnaryAssignable<Type.EffectiveTuple> {
		public final int index;

		private TupleLoad(Type.EffectiveTuple type, int target, int operand,
				int index) {
			super(type, target, operand);
			this.index = index;
		}

		@Override
		public int opcode() {
			return OPCODE_tupleload;
		}

		public Type assignedType() {
			return type().element(index);
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return TupleLoad(type(), nTarget, nOperands[0], index);
		}

		public boolean equals(Object o) {
			if (o instanceof TupleLoad) {
				TupleLoad i = (TupleLoad) o;
				return index == i.index && super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "tupleload %" + target() + " = %" + operand(0) + " " + index
					+ " : " + type();
		}
	}

	/**
	 * Reads a reference value from the operand register, dereferences it (i.e.
	 * extracts the value it refers to) and writes this to the target register.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class Dereference extends
			AbstractUnaryAssignable<Type.Reference> {

		private Dereference(Type.Reference type, int target, int operand) {
			super(type, target, operand);
		}

		@Override
		public int opcode() {
			return OPCODE_dereference;
		}

		public Type assignedType() {
			return type().element();
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return Dereference(type(), nTarget, nOperands[0]);
		}

		public boolean equals(Object o) {
			if (o instanceof Dereference) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "deref %" + target() + " = %" + operand(0) + " : " + type();
		}
	}

	public enum UnaryOperatorKind {
		NEG(0) {
			public String toString() {
				return "neg";
			}
		},

		NUMERATOR(1) {
			public String toString() {
				return "num";
			}
		},

		DENOMINATOR(2) {
			public String toString() {
				return "den";
			}
		};
		public final int offset;

		private UnaryOperatorKind(int offset) {
			this.offset = offset;
		}
	};

	/**
	 * Read a number (int or real) from the operand register, perform a unary
	 * arithmetic operation on it (e.g. negation) and writes the result to the
	 * target register. For example, the following Whiley code:
	 *
	 * <pre>
	 * function f(int x) => int:
	 *     return -x
	 * </pre>
	 *
	 * can be translated into the following WyIL:
	 *
	 * <pre>
	 * function f(int x) => int:
	 * body:
	 *     neg %0 = %0     : int
	 *     return %0       : int
	 * </pre>
	 *
	 * This simply reads the parameter <code>x</code> stored in register
	 * <code>%0</code>, negates it and then returns the negated value.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class UnaryOperator extends AbstractUnaryAssignable<Type> {
		public final UnaryOperatorKind kind;

		private UnaryOperator(Type type, int target, int operand, UnaryOperatorKind uop) {
			super(type, target, operand);
			if (uop == null) {
				throw new IllegalArgumentException(
						"UnaryArithOp bop argument cannot be null");
			}
			this.kind = uop;
		}

		@Override
		public int opcode() {
			return OPCODE_neg + kind.offset;
		}

		@Override
		public Code.Unit clone(int nTarget, int[] nOperands) {
			return UnaryOperator(type(), nTarget, nOperands[0], kind);
		}

		public int hashCode() {
			return kind.hashCode() + super.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof UnaryOperator) {
				UnaryOperator bo = (UnaryOperator) o;
				return kind.equals(bo.kind) && super.equals(bo);
			}
			return false;
		}

		public String toString() {
			return kind + " %" + target() + " = %" + operand(0) + " : " + type();
		}
	}

	/**
	 * The void bytecode is used to indicate that the given register(s) are no
	 * longer live. This is useful for communicating information to the memory
	 * management system about which values could in principle be collected.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Void extends AbstractNaryAssignable<Type> {

		private Void(Type type, int[] operands) {
			super(type, Codes.NULL_REG, operands);
		}

		@Override
		public int opcode() {
			return OPCODE_void;
		}

		protected Code.Unit clone(int nTarget, int[] nOperands) {
			return Void(type(), nOperands);
		}

		public Type assignedType() {
			return Type.T_VOID;
		}

		public boolean equals(Object o) {
			if (o instanceof Void) {
				return super.equals(o);
			}
			return false;
		}

		public String toString() {
			return "void " + arrayToString(operands());
		}
	}

	// =============================================================
	// Helpers
	// =============================================================
	private static int[] append(int[] operands, int operand) {
		int[] noperands = Arrays.copyOf(operands, operands.length+1);
		noperands[operands.length] = operand;
		return noperands;
	}

	private static int[] append(int operand, int[] operands) {
		int[] noperands = new int[operands.length+1];
		System.arraycopy(operands,0,noperands,1,operands.length);
		noperands[0] = operand;
		return noperands;
	}

	private static final ArrayList<Code> values = new ArrayList<Code>();
	private static final HashMap<Code, Integer> cache = new HashMap<Code, Integer>();

	private static <T extends Code> T get(T type) {
		Integer idx = cache.get(type);
		if (idx != null) {
			return (T) values.get(idx);
		} else {
			cache.put(type, values.size());
			values.add(type);
			return type;
		}
	}
}

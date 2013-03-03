package wycs.transforms;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import static wybs.lang.SyntaxError.*;
import wybs.lang.Attribute;
import wybs.lang.Builder;
import wybs.lang.NameID;
import wybs.lang.Transform;
import wybs.util.Pair;
import wybs.util.ResolveError;
import wycs.WycsBuilder;
import wycs.lang.*;

public class ConstraintInline implements Transform<WycsFile> {
	
	/**
	 * Determines whether constraint inlining is enabled or not.
	 */
	private boolean enabled = getEnable();

	private final WycsBuilder builder;
	
	private String filename;

	// ======================================================================
	// Constructor(s)
	// ======================================================================
	
	public ConstraintInline(Builder builder) {
		this.builder = (WycsBuilder) builder;
	}
	
	// ======================================================================
	// Configuration Methods
	// ======================================================================

	public static String describeEnable() {
		return "Enable/disable constraint inlining";
	}

	public static boolean getEnable() {
		return true; // default value
	}

	public void setEnable(boolean flag) {
		this.enabled = flag;
	}

	// ======================================================================
	// Apply Method
	// ======================================================================

	public void apply(WycsFile wf) {
		if(enabled) {
			this.filename = wf.filename();
			for(WycsFile.Declaration s : wf.declarations()) {
				transform(s);
			}
		}
	}
	
	private void transform(WycsFile.Declaration s) {
		if(s instanceof WycsFile.Function) {
			WycsFile.Function sf = (WycsFile.Function) s;
			transform(sf);
		} else if(s instanceof WycsFile.Assert) {
			transform((WycsFile.Assert)s);
		} else if(s instanceof WycsFile.Import) {
			// can ignore for now
		} else {
			internalFailure("unknown declaration encountered (" + s + ")",
					filename, s);
		}
	}
	
	private void transform(WycsFile.Function s) {
		s.condition = transformCondition(s.condition,s);
	}
	
	private void transform(WycsFile.Assert s) {
		s.expr = transformCondition(s.expr,s);
	}
	
	private Expr transformCondition(Expr e, WycsFile.Context context) {
		if (e instanceof Expr.Variable || e instanceof Expr.Constant) {
			// do nothing
			return e;
		} else if (e instanceof Expr.Unary) {
			return transformCondition((Expr.Unary)e, context);
		} else if (e instanceof Expr.Binary) {
			return transformCondition((Expr.Binary)e, context);
		} else if (e instanceof Expr.Nary) {
			return transformCondition((Expr.Nary)e, context);
		} else if (e instanceof Expr.Quantifier) {
			return transformCondition((Expr.Quantifier)e, context);
		} else if (e instanceof Expr.FunCall) {
			return transformCondition((Expr.FunCall)e, context);
		} else {
			internalFailure("invalid boolean expression encountered (" + e
					+ ")", filename, e);
			return null;
		}
	}
	
	private Expr transformCondition(Expr.Unary e, WycsFile.Context context) {
		switch(e.op) {
		case NOT:
			e.operand = transformCondition(e.operand, context);
			return e;
		default:
			internalFailure("invalid boolean expression encountered (" + e
					+ ")", filename, e);
			return null;
		}
	}
	
	private Expr transformCondition(Expr.Binary e, WycsFile.Context context) {
		switch (e.op) {
		case EQ:
		case NEQ:
		case LT:
		case LTEQ:
		case GT:
		case GTEQ:
		case IN:
		case SUBSET:
		case SUBSETEQ:
		case SUPSET:
		case SUPSETEQ: {
			ArrayList<Expr> assumptions = new ArrayList<Expr>();
			transformExpression(e, assumptions, context);
			if (assumptions.size() > 0) {
				Expr lhs = Expr.Nary(Expr.Nary.Op.AND, assumptions,
						e.attribute(Attribute.Source.class));				
				return Expr.Binary(Expr.Binary.Op.IMPLIES, lhs,e,
						e.attribute(Attribute.Source.class));
			} else {
				return e;
			}
		}
		case IMPLIES:
		case IFF: {
			e.leftOperand = transformCondition(e.leftOperand, context);
			e.rightOperand = transformCondition(e.rightOperand, context);
			return e;
		}
		default:
			internalFailure("invalid boolean expression encountered (" + e
					+ ")", filename, e);
			return null;
		}
	}
	
	private Expr transformCondition(Expr.Nary e, WycsFile.Context context) {
		switch(e.op) {
		case AND:
		case OR: {
			Expr[] e_operands = e.operands;
			for(int i=0;i!=e_operands.length;++i) {
				e_operands[i] = transformCondition(e_operands[i], context);
			}
			return e;
		}		
		default:
			internalFailure("invalid boolean expression encountered (" + e
					+ ")", filename, e);
			return null;
		}
	}
	
	private Expr transformCondition(Expr.Quantifier e, WycsFile.Context context) {
		e.operand = transformCondition(e.operand, context);
		return e;
	}
	
	private Expr transformCondition(Expr.FunCall e, WycsFile.Context context) {
		try {
			Pair<NameID, WycsFile.Function> p = builder.resolveAs(e.name,
					WycsFile.Function.class, context);
			WycsFile.Function fn = p.second();
			if (fn instanceof WycsFile.Define) {
				if (fn.condition == null) {
					internalFailure("predicate defined without a condition?",
							filename, e);
				}
				HashMap<String, Expr> binding = new HashMap<String, Expr>();
				bind(e.operand, fn.from, binding);
				return substitute(fn.condition, binding);
			} else {
				Expr r = e;
				if (fn.condition != null) {

					HashMap<String, Expr> binding = new HashMap<String, Expr>();
					bind(e.operand, fn.from, binding);
					// TODO: make this more general?
					bind(e, fn.to, binding);
					r = Expr.Nary(
							Expr.Nary.Op.AND,
							new Expr[] { e, substitute(fn.condition, binding) },
							e.attribute(Attribute.Source.class));
				}
				
				ArrayList<Expr> assumptions = new ArrayList<Expr>();
				transformExpression(e, assumptions, context);
				if (assumptions.size() > 0) {
					Expr lhs = Expr.Nary(Expr.Nary.Op.AND, assumptions,
							e.attribute(Attribute.Source.class));				
					return Expr.Binary(Expr.Binary.Op.IMPLIES, lhs,r,
							e.attribute(Attribute.Source.class));
				} else {
					return r;
				}
			} 
		} catch(ResolveError re) {
			internalFailure(re.getMessage(),filename,context,re);
			return null;
		}
	}
	
	private void transformExpression(Expr e, ArrayList<Expr> constraints, WycsFile.Context context) {
		if (e instanceof Expr.Variable || e instanceof Expr.Constant) {
			// do nothing
		} else if (e instanceof Expr.Unary) {
			transformExpression((Expr.Unary)e,constraints,context);
		} else if (e instanceof Expr.Binary) {
			transformExpression((Expr.Binary)e,constraints,context);
		} else if (e instanceof Expr.Nary) {
			transformExpression((Expr.Nary)e,constraints,context);
		} else if (e instanceof Expr.FunCall) {
			transformExpression((Expr.FunCall)e,constraints,context);
		} else {
			internalFailure("invalid expression encountered (" + e
					+ ")", filename, e);
		}
	}
	
	private void transformExpression(Expr.Unary e, ArrayList<Expr> constraints, WycsFile.Context context) {
		switch (e.op) {
		case NOT:
		case NEG:
		case LENGTHOF:
			transformExpression(e.operand,constraints,context);
			break;
		default:
			internalFailure("invalid unary expression encountered (" + e
					+ ")", filename, e);			
		}
	}
	
	private void transformExpression(Expr.Binary e, ArrayList<Expr> constraints, WycsFile.Context context) {
		switch (e.op) {
		case ADD:
		case SUB:
		case MUL:
		case DIV:
		case REM:
		case EQ:
		case NEQ:
		case IMPLIES:
		case IFF:
		case LT:
		case LTEQ:
		case GT:
		case GTEQ:
		case IN:
		case SUBSET:
		case SUBSETEQ:
		case SUPSET:
		case SUPSETEQ:
			transformExpression(e.leftOperand,constraints,context);
			transformExpression(e.rightOperand,constraints,context);
			break;
		default:
			internalFailure("invalid binary expression encountered (" + e
					+ ")", filename, e);			
		}
	}
	
	private void transformExpression(Expr.Nary e, ArrayList<Expr> constraints, WycsFile.Context context) {
		switch(e.op) {
		case AND:
		case OR:
		case SET:
		case TUPLE: {
			Expr[] e_operands = e.operands;
			for(int i=0;i!=e_operands.length;++i) {
				transformExpression(e_operands[i],constraints,context);
			}
			break;
		}				
		default:
			internalFailure("invalid nary expression encountered (" + e
					+ ")", filename, e);
		}
	}
	
	private void transformExpression(Expr.FunCall e,
			ArrayList<Expr> constraints, WycsFile.Context context) {
		transformExpression(e.operand,constraints,context);
		try {
			Pair<NameID,WycsFile.Function> p = builder.resolveAs(e.name,WycsFile.Function.class,context);
			WycsFile.Function fn = p.second();
			if(fn.condition != null) {
				HashMap<String,Expr> binding = new HashMap<String,Expr>();
				bind(e.operand,fn.from,binding);
				// TODO: make this more general?
				bind(e,fn.to,binding);	
				constraints.add(substitute(fn.condition,binding));
			}
		} catch(ResolveError re) {
			internalFailure(re.getMessage(),filename,context,re);
		}
	}
	
	private void bind(Expr operand, SyntacticType t, HashMap<String,Expr> binding) {
		if(t.name != null) {
			binding.put(t.name,operand);
		}
		if (t instanceof SyntacticType.Tuple && operand instanceof Expr.Nary) {
			SyntacticType.Tuple tt = (SyntacticType.Tuple)t;
			Expr.Nary tc = (Expr.Nary) operand;
			if(tt.elements.size() != tc.operands.length || tc.op != Expr.Nary.Op.TUPLE) {
				internalFailure("cannot bind function call to declaration", filename, operand);
			}
			ArrayList<SyntacticType> parameters = tt.elements;
			Expr[] arguments = tc.operands;
			for(int i=0;i!=arguments.length;++i) {
				bind(arguments[i],parameters.get(i),binding);
			}
		}		
	}
	
	private Expr substitute(Expr e, HashMap<String,Expr> binding) {		
		if (e instanceof Expr.Constant) {
			// do nothing		
			return e;
		} else if (e instanceof Expr.Variable) {
			return substitute((Expr.Variable)e,binding);
		} else if (e instanceof Expr.Unary) {
			return substitute((Expr.Unary)e,binding);
		} else if (e instanceof Expr.Binary) {
			return substitute((Expr.Binary)e,binding);
		} else if (e instanceof Expr.Nary) {
			return substitute((Expr.Nary)e,binding);
		} else if (e instanceof Expr.FunCall) {
			return substitute((Expr.FunCall)e,binding);
		} else if (e instanceof Expr.Quantifier) {
			return substitute((Expr.Quantifier)e,binding);
		} else {
			internalFailure("invalid expression encountered (" + e
					+ ")", filename, e);
			return null;
		}
	}
	
	private Expr substitute(Expr.Variable e, HashMap<String,Expr> binding) {
		Expr r = binding.get(e.name);
		if(r != null) {
			// FIXME: should clone here!!!
			return r;
		} else {
			return e;
		}
	}
	
	private Expr substitute(Expr.Unary e, HashMap<String,Expr> binding) {
		switch (e.op) {
		case NOT:
		case NEG:
		case LENGTHOF:
			Expr expr = substitute(e.operand,binding);
			return Expr.Unary(e.op, expr, e.attributes());
		default:
			internalFailure("invalid unary expression encountered (" + e
					+ ")", filename, e);
			return null;
		}
	}
	
	private Expr substitute(Expr.Binary e, HashMap<String,Expr> binding) {
		switch (e.op) {
		case ADD:
		case SUB:
		case MUL:
		case DIV:
		case REM:
		case EQ:
		case NEQ:
		case IMPLIES:
		case IFF:
		case LT:
		case LTEQ:
		case GT:
		case GTEQ:
		case IN:
		case SUBSET:
		case SUBSETEQ:
		case SUPSET:
		case SUPSETEQ:		
			Expr lhs = substitute(e.leftOperand,binding);
			Expr rhs = substitute(e.rightOperand,binding);
			return Expr.Binary(e.op, lhs, rhs, e.attributes());
		default:
			internalFailure("invalid binary expression encountered (" + e
					+ ")", filename, e);			
			return null;
		}				
	}
	
	private Expr substitute(Expr.Nary e, HashMap<String,Expr> binding) {
		switch(e.op) {
		case AND:
		case OR:
		case SET:
		case TUPLE: {
			Expr[] e_operands = e.operands;
			Expr[] r_operands = new Expr[e_operands.length];
			for(int i=0;i!=e_operands.length;++i) {
				r_operands[i] = substitute(e_operands[i],binding);
			}
			return Expr.Nary(e.op, r_operands, e.attributes());
		}				
		default:
			internalFailure("invalid nary expression encountered (" + e
					+ ")", filename, e);
			return null;
		}
	}
	
	private Expr substitute(Expr.FunCall e, HashMap<String,Expr> binding) {
		Expr operand = substitute(e.operand,binding);		
		return Expr.FunCall(e.name, e.generics, operand, e.attributes());
	}
	
	private Expr substitute(Expr.Quantifier e, HashMap<String,Expr> binding) {
		List<Pair<String,Expr>> boundedVariables = e.boundedVariables;
		ArrayList<Pair<String,Expr>> nBoundedVariables = new ArrayList<Pair<String,Expr>>();
		for(Pair<String,Expr> p : boundedVariables) {
			nBoundedVariables.add(new Pair<String,Expr>(p.first(),substitute(p.second(),binding)));
		}
		
		Expr operand = substitute(e.operand,binding);		
		
		// FIXME: there is a potential problem here for variable capture.
		
		if(e instanceof Expr.ForAll) {
			return Expr.ForAll(e.unboundedVariables,nBoundedVariables,operand,e.attributes());
		} else {
			return Expr.Exists(e.unboundedVariables,nBoundedVariables,operand,e.attributes());
		}
	}
}
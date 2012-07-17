package wyc.builder;

import java.util.*;

import static wyc.lang.WhileyFile.*;
import wyil.lang.*;
import wybs.lang.Path;
import wybs.util.ResolveError;
import wyc.lang.UnresolvedType;
import wyc.lang.WhileyFile;

/**
 * <p>
 * The global generator is responsible for generating wyil bytecode for "global"
 * items. Essentially, this comes down to type constraints and partial
 * constants. For example:
 * </p>
 * 
 * <pre>
 * define nat as int where $ >= 0
 * 
 * int f(nat x):
 *    return x-1
 * </pre>
 * 
 * <p>
 * The global generator is responsible for generating the code for the
 * constraint on <code>nat</code>. Note, local generator are responsible for
 * inlining that constraint into the body of function <code>f</code>.
 * </p>
 * 
 * <p>
 * The code generated by the global generator for the constraint on
 * <code>nat</code> would look like this:
 * </p>
 * 
 * <pre>
 * define nat as int
 * where:
 *     load $
 *     const 0
 *     ifge goto exit
 *     fail("type constraint not satisfied")
 *  .exit:
 * </pre>
 * 
 * This wyil bytecode simply compares the special variable $ against 0. Here, $
 * represents the value held in a variable of type <code>nat</code>. If the
 * constraint fails, then the given message is printed.
 * 
 * @author David J. Pearce
 * 
 */
public class GlobalGenerator {
	private final WhileyBuilder builder;
	private final GlobalResolver resolver;	
	private final HashMap<NameID,Block> cache = new HashMap<NameID,Block>();
	
	public GlobalGenerator(WhileyBuilder builder, GlobalResolver resolver) {		
		this.builder = builder;
		this.resolver = resolver;
	}
		
	public Block generate(NameID nid) throws Exception {
		Block blk = cache.get(nid);
		if(blk == EMPTY_BLOCK) {
			return null;
		} else if(blk != null) {
			return blk;
		}
		
		// check whether the item in question is in one of the source
		// files being compiled.
		Path.ID mid = nid.module();
		WhileyFile wf = builder.getSourceFile(mid);
		if(wf != null) {
			// FIXME: the following line is necessary to terminate infinite
			// recursion. However, we really need to do better in the
			// context of recurisve types with constraints.
	
			WhileyFile.TypeDef td = wf.typeDecl(nid.name());
			if(td != null) {
				cache.put(nid, EMPTY_BLOCK);
				blk = generate(td.unresolvedType,td);
				if(td.constraint != null) {								
					if(blk == null) {
						blk = new Block(1);					
					}
					HashMap<String,Integer> environment = new HashMap<String,Integer>();
					environment.put("$",Code.REG_0);
					addExposedNames(td.resolvedType.raw(),environment,blk);
					blk.append(new LocalGenerator(this, td).generateAssertion(
							"constraint not satisfied", td.constraint, false,
							environment.size(), environment));
				}
				cache.put(nid, blk);
				return blk;
			} else {
				Value v = resolver.resolveAsConstant(nid);				
				if(v instanceof Value.Set) {
					Value.Set vs = (Value.Set) v;
					Type.Set type = vs.type();
					blk = new Block(1);					
					blk.append(Code.Const(Code.REG_1, v));
					blk.append(Code.Assert(vs.type(), Code.REG_0, Code.REG_1,
							Code.Comparator.ELEMOF, "constraint not satisfied"));
					cache.put(nid, blk);
					return blk;
				} 
			}			
		} else {
			// now check whether it's already compiled and available on the
			// WHILEYPATH.
			WyilFile m = builder.getModule(mid);
			WyilFile.TypeDeclaration td = m.type(nid.name());
			if(td != null) {
				// should I cache this?
				return td.constraint();
			} else {
				return null;
			}
		}
		
		// FIXME: better error message?
		throw new ResolveError("name not found: " + nid);
	}
	
	public Block generate(UnresolvedType t, Context context) throws Exception {
		Nominal nt = resolver.resolveAsType(t, context);
		Type raw = nt.raw();
		if (t instanceof UnresolvedType.List) {
			UnresolvedType.List lt = (UnresolvedType.List) t;
			Block blk = generate(lt.element, context);			
			if (blk != null) {
				Block nblk = new Block(1);
				String label = Block.freshLabel();
				nblk.append(Code.ForAll((Type.EffectiveCollection) raw,
						Code.REG_0, Code.REG_1, Collections.EMPTY_LIST, label),
						t.attributes());
				nblk.append(shiftBlock(1, blk));
				nblk.append(Code.End(label));
				blk = nblk;
			}
			return blk;
		} else if (t instanceof UnresolvedType.Set) {
			UnresolvedType.Set st = (UnresolvedType.Set) t;
			Block blk = generate(st.element, context);
			if (blk != null) {
				Block nblk = new Block(1);
				String label = Block.freshLabel();
				nblk.append(Code.ForAll((Type.EffectiveCollection) raw,
						Code.REG_0, Code.REG_1, Collections.EMPTY_LIST, label),
						t.attributes());
				nblk.append(shiftBlock(1, blk));
				nblk.append(Code.End(label));
				blk = nblk;
			}
			return blk;
		} else if (t instanceof UnresolvedType.Map) {
			UnresolvedType.Map st = (UnresolvedType.Map) t;
			Block blk = null;
			// FIXME: put in constraints. REQUIRES ITERATION OVER DICTIONARIES
			Block key = generate(st.key, context);
			Block value = generate(st.value, context);
			return blk;
		} else if (t instanceof UnresolvedType.Tuple) {
			// At the moment, a tuple is compiled down to a wyil record.
			UnresolvedType.Tuple tt = (UnresolvedType.Tuple) t;
			Type.EffectiveTuple ett = (Type.EffectiveTuple) raw;
			List<Type> ettElements = ett.elements();
			Block blk = null;
			
			int i = 0;
			for (UnresolvedType e : tt.types) {
				Block p = generate(e, context);
				if (p != null) {
					if (blk == null) {
						blk = new Block(1);
					}
					blk.append(Code.TupleLoad(ett, Code.REG_1, Code.REG_0, i),
							t.attributes());
					blk.append(shiftBlock(1, p));
				}
				i = i + 1;
			}

			return blk;
		} else if (t instanceof UnresolvedType.Record) {
			UnresolvedType.Record tt = (UnresolvedType.Record) t;
			Type.EffectiveRecord ert = (Type.EffectiveRecord) raw;
			Map<String,Type> fields = ert.fields();
			Block blk = null;			
			for (Map.Entry<String, UnresolvedType> e : tt.types.entrySet()) {
				Block p = generate(e.getValue(), context);
				if (p != null) {
					if (blk == null) {
						blk = new Block(1);
					}					
					blk.append(
							Code.FieldLoad(ert, Code.REG_1, Code.REG_0,
									e.getKey()), t.attributes());
					blk.append(shiftBlock(1, p));
				}
			}
			return blk;
		} else if (t instanceof UnresolvedType.Union) {
			UnresolvedType.Union ut = (UnresolvedType.Union) t;			
			
			boolean constraints = false;
			DecisionTree tree = new DecisionTree(raw);
			
			for (UnresolvedType b : ut.bounds) {
				Type type = resolver.resolveAsType(b, context).raw();
				Block constraint = generate(b, context);
				constraints |= constraint != null;
				tree.add(type,constraint);
			}
			
			if(constraints) {
				return tree.flattern();
			} else {
				// no constraints, must not do anything!
				return null;
			}
		} else if (t instanceof UnresolvedType.Not) {
			UnresolvedType.Not st = (UnresolvedType.Not) t;
			Block p = generate(st.element, context);
			Block blk = null;
			// TODO: need to fix not constraints
			return blk;
		} else if (t instanceof UnresolvedType.Intersection) {
			UnresolvedType.Intersection ut = (UnresolvedType.Intersection) t;
			Block blk = null;			
			for (int i = 0; i != ut.bounds.size(); ++i) {
				UnresolvedType b = ut.bounds.get(i);
				Block p = generate(b, context);
				// TODO: add intersection constraints				
			}
			return blk;
		} else if (t instanceof UnresolvedType.Reference) {
			UnresolvedType.Reference ut = (UnresolvedType.Reference) t;			
			Block blk = generate(ut.element, context);
			// TODO: fix process constraints
			return null;
		} else if (t instanceof UnresolvedType.Nominal) {
			UnresolvedType.Nominal dt = (UnresolvedType.Nominal) t;
			
			try {
				NameID nid = resolver.resolveAsName(dt.names,context);
				return generate(nid);
			} catch (ResolveError rex) {
				syntaxError(rex.getMessage(), context, t, rex);
				return null;
			}
		} else {
			// for base cases
			return null;
		}
	}
	
	/**
	 * The shiftBlock method takes a block and shifts every slot a given amount
	 * to the right. The number of inputs remains the same. This method is used 
	 * 
	 * @param amount
	 * @param blk
	 * @return
	 */
	private static Block shiftBlock(int amount, Block blk) {
		HashMap<Integer,Integer> binding = new HashMap<Integer,Integer>();
		for(int i=0;i!=blk.numSlots();++i) {
			binding.put(i,i+amount);
		}
		Block nblock = new Block(blk.numInputs());
		for(Block.Entry e : blk) {
			Code code = e.code.remap(binding);
			nblock.append(code,e.attributes());
		}
		return nblock.relabel();
	}
	
	/**
	 * The purpose of this method is to capture the case when we have a define
	 * statement like this:
	 * 
	 * <pre>
	 * define tup as {int x, int y} where x < y
	 * </pre>
	 * 
	 * We say that <code>x</code> and <code>y</code> are "exposed" --- meaning
	 * their real names are different in some way. In this case, the aliases we
	 * have are: x->$.x and y->$.y.  
	 * 
	 * @param src
	 * @param t
	 * @param environment
	 */
	private void addExposedNames(Type t, HashMap<String, Integer> environment,
			Block blk) {
		// Extending this method to handle lists and sets etc, is very
		// difficult. The primary problem is that we need to expand expressions
		// involving names exposed in this way into quantified expressions (or
		// something).
		if (t instanceof Type.Record) {
			Type.Record tt = (Type.Record) t;
			for (Map.Entry<String, Type> e : tt.fields().entrySet()) {
				String field = e.getKey();
				Integer i = environment.get(field);
				if (i == null) {
					int target = environment.size();
					environment.put(field, target);
					blk.append(Code.FieldLoad(tt, target, Code.REG_0, field));
				}
			}
		}
	}
	
	private static final Block EMPTY_BLOCK = new Block(1);
}

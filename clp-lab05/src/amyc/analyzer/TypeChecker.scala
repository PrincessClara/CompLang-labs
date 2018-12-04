package amyc
package analyzer

import utils._
import ast.SymbolicTreeModule._
import ast.Identifier

// The type checker for Amy
// Takes a symbolic program and rejects it if it does not follow the Amy typing rules.
object TypeChecker extends Pipeline[(Program, SymbolTable), (Program, SymbolTable)] {

  def run(ctx: Context)(v: (Program, SymbolTable)): (Program, SymbolTable) = {
    import ctx.reporter._

    val (program, table) = v

    case class Constraint(found: Type, expected: Type, pos: Position)

    // Represents a type variable.
    // It extends Type, but it is meant only for internal type checker use,
    //  since no Amy value can have such type.
    case class TypeVariable private (id: Int) extends Type
    object TypeVariable {
      private val c = new UniqueCounter[Unit]
      def fresh(): TypeVariable = TypeVariable(c.next(()))
    }

    // Generates typing constraints for an expression `e` with a given expected type.
    // The environment `env` contains all currently available bindings (you will have to
    //  extend these, e.g., to account for local variables).
    // Returns a list of constraints among types. These will later be solved via unification.
    def genConstraints(e: Expr, expected: Type)(implicit env: Map[Identifier, Type]): List[Constraint] = {
      
      // This helper returns a list of a single constraint recording the type
      //  that we found (or generated) for the current expression `e`
      def topLevelConstraint(found: Type): List[Constraint] =
        List(Constraint(found, expected, e.position))
      
      e match {
        case Variable(name) =>
          val t = env.get(name).get
          topLevelConstraint(t)
        
        case IntLiteral(_) =>
          topLevelConstraint(IntType)
          
        case BooleanLiteral(_) =>
          topLevelConstraint(BooleanType)
          
        case StringLiteral(_) =>
          topLevelConstraint(StringType)
          
        case UnitLiteral() =>
          topLevelConstraint(UnitType)
          
        case Plus(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: genConstraints(rhs, IntType) ::: topLevelConstraint(IntType)
          
        case Minus(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: genConstraints(rhs, IntType) ::: topLevelConstraint(IntType)
          
        case Times(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: genConstraints(rhs, IntType) ::: topLevelConstraint(IntType)
          
        case Div(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: genConstraints(rhs, IntType) ::: topLevelConstraint(IntType)
          
        case Mod(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: genConstraints(rhs, IntType) ::: topLevelConstraint(IntType)
          
        case LessThan(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: genConstraints(rhs, IntType) ::: topLevelConstraint(BooleanType)
          
        case LessEquals(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: genConstraints(rhs, IntType) ::: topLevelConstraint(BooleanType)
          
        case And(lhs, rhs) =>
          genConstraints(lhs, BooleanType) ::: genConstraints(rhs, BooleanType) ::: topLevelConstraint(BooleanType)
          
        case Or(lhs, rhs) =>
          genConstraints(lhs, BooleanType) ::: genConstraints(rhs, BooleanType) ::: topLevelConstraint(BooleanType)
        
        case Equals(lhs, rhs) =>
          // HINT: Take care to implement the specified Amy semantics
          val t = TypeVariable.fresh()
          genConstraints(lhs, t) ::: genConstraints(rhs, t) ::: topLevelConstraint(BooleanType)
          
        case Concat(lhs, rhs) =>
          genConstraints(lhs, StringType) ::: genConstraints(rhs, StringType) ::: topLevelConstraint(StringType)
          
        case Not(e) =>
          genConstraints(e, BooleanType) ::: topLevelConstraint(BooleanType)
          
        case Neg(e) =>
          genConstraints(e, IntType) ::: topLevelConstraint(IntType)
          
        case Call(qname, args) =>
          val sig = table.getConstructor(qname).getOrElse(table.getFunction(qname).get)
          val ts = sig.argTypes
          val rt = sig.retType
          def checkArgs(args: List[Expr], types: List[Type]): List[Constraint] = args match {
            case e :: Nil => genConstraints(e, types.head)
            case e :: rest => genConstraints(e, types.head) ::: checkArgs(rest, types.tail)
          }
          checkArgs(args, ts) ::: topLevelConstraint(rt)

        case Sequence(e1, e2) =>
          val t1 = TypeVariable.fresh()
          val t2 = TypeVariable.fresh()
          genConstraints(e1, t1) ::: genConstraints(e2, t2) ::: topLevelConstraint(t2)
          
        case Let(df, value, body) =>
          val name = df.name
          val t1 = df.tt.tpe
          val t2 = TypeVariable.fresh()
          genConstraints(value, t1) ::: genConstraints(body, t2)(env ++ Map(name -> t1)) ::: topLevelConstraint(t2)
          
        case Ite(cond, thenn, elze) =>
          val t = TypeVariable.fresh()
          genConstraints(cond, BooleanType) ::: genConstraints(thenn, t) ::: genConstraints(elze, t) ::: topLevelConstraint(t)
        
        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          def handlePattern(pat: Pattern, scrutExpected: Type):
            (List[Constraint], Map[Identifier, Type]) = pat match
          {
            case WildcardPattern() =>
              (List(), Map())
            case IdPattern(name) =>
              (List(), Map(name -> scrutExpected))
            case LiteralPattern(lit) =>
              lit match {
                case IntLiteral(_) => (List(Constraint(IntType, scrutExpected, e.position)), Map())
                case BooleanLiteral(_) => (List(Constraint(BooleanType, scrutExpected, e.position)), Map())
                case StringLiteral(_) => (List(Constraint(StringType, scrutExpected, e.position)), Map())
                case UnitLiteral() => (List(Constraint(UnitType, scrutExpected, e.position)), Map())
              }
            case CaseClassPattern(qn, args) =>
              val sig = table.getConstructor(qn).getOrElse(table.getFunction(qn).get)
              val types = sig.argTypes
              val argsts = args.zip(types)
              val rt = sig.retType
              val x = argsts.map { case (arg,t) => handlePattern(arg, t) }.unzip
              (x._1.flatten ++ List(Constraint(rt, scrutExpected, e.position)), x._2.flatten.toMap)
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            genConstraints(cse.expr, expected)(env ++ moreEnv) ::: patConstraints
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))

        case Error(msg) =>
          genConstraints(msg, StringType) ::: topLevelConstraint(TypeVariable.fresh())
      }
    }


    // Given a list of constraints `constraints`, replace every occurence of type variable
    //  with id `from` by type `to`.
    def subst_*(constraints: List[Constraint], from: Int, to: Type): List[Constraint] = {
      // Do a single substitution.
      def subst(tpe: Type, from: Int, to: Type): Type = {
        tpe match {
          case TypeVariable(`from`) => to
          case other => other
        }
      }

      constraints map { case Constraint(found, expected, pos) =>
        Constraint(subst(found, from, to), subst(expected, from, to), pos)
      }
    }

    // Solve the given set of typing constraints and
    //  call `typeError` if they are not satisfiable.
    // We consider a set of constraints to be satisfiable exactly if they unify.
    def solveConstraints(constraints: List[Constraint]): Unit = {
      constraints match {
        case Nil => ()
        case Constraint(found, expected, pos) :: more =>
          // HINT: You can use the `subst_*` helper above to replace a type variable
          //       by another type in your current set of constraints.
          (found, expected) match {
            case (tpe1@TypeVariable(t1), tpe2@TypeVariable(t2)) =>
              solveConstraints(subst_*(more, t1, tpe2) ++ List(Constraint(tpe2, tpe2, pos)))
            case (TypeVariable(t1), t2) =>
              solveConstraints(subst_*(more, t1, t2))
            case (t1, TypeVariable(t2)) =>
              solveConstraints(subst_*(more, t2, t1))
            case (t1, t2) =>
              if(t1 != t2) error(s"Type error: expected: $t2, found: $t1", pos)
              solveConstraints(more)
          }
      }
    }

    // Putting it all together to type-check each module's functions and main expression.
    program.modules.foreach { mod =>
      // Put function parameters to the symbol table, then typecheck them against the return type
      mod.defs.collect { case FunDef(_, params, retType, body) =>
        val env = params.map{ case ParamDef(name, tt) => name -> tt.tpe }.toMap
        solveConstraints(genConstraints(body, retType.tpe)(env))
      }

      // Type-check expression if present. We allow the result to be of an arbitrary type by
      // passing a fresh (and therefore unconstrained) type variable as the expected type.
      val tv = TypeVariable.fresh()
      mod.optExpr.foreach(e => solveConstraints(genConstraints(e, tv)(Map())))
    }

    v

  }
}

package amyc
package analyzer

import utils._
import ast.{Identifier, NominalTreeModule => N, SymbolicTreeModule => S}

// Name analyzer for Amy
// Takes a nominal program (names are plain strings, qualified names are string pairs)
// and returns a symbolic program, where all names have been resolved to unique Identifiers.
// Rejects programs that violate the Amy naming rules.
// Also populates and returns the symbol table.
object NameAnalyzer extends Pipeline[N.Program, (S.Program, SymbolTable)] {
  def run(ctx: Context)(p: N.Program): (S.Program, SymbolTable) = {
    import ctx.reporter._

    // Step 0: Initialize symbol table
    val table = new SymbolTable

    // Step 1: Add modules to table 
    val modNames = p.modules.groupBy(_.name)
    modNames.foreach { case (name, modules) =>
      if (modules.size > 1) {
        fatal(s"Two modules named $name in program", modules.head.position)
      }
    }

    modNames.keys.toList foreach table.addModule


    // Helper method: will transform a nominal type 'tt' to a symbolic type,
    // given that we are within module 'inModule'.
    def transformType(tt: N.TypeTree, inModule: String): S.Type = {
      tt.tpe match {
        case N.IntType => S.IntType
        case N.BooleanType => S.BooleanType
        case N.StringType => S.StringType
        case N.UnitType => S.UnitType
        case N.ClassType(qn@N.QualifiedName(module, name)) =>
          table.getType(module getOrElse inModule, name) match {
            case Some(symbol) =>
              S.ClassType(symbol)
            case None =>
              fatal(s"Could not find type $qn", tt)
          }
      }
    }

    // Step 2: Check name uniqueness of definitions in each module
    var definitions : List[(N.ClassOrFunDef, String)] = List()
    modNames.foreach { case (name, module) =>
      val defNames = module.head.defs.groupBy(_.name)
      defNames.foreach { case (name, defs) =>
        val mod = module.head.name
        if (defs.size > 1) {
          fatal(s"Two definitions named $name in module $mod", defs.head.position)
        }
        definitions = (defs.head, mod) :: definitions
      }
    }

    for(d <- definitions) {
      d match { 
        // Step 3: Discover types and add them to symbol table
        case (N.AbstractClassDef(name), mod) => table.addType(mod, name)
        // Step 4: Discover type constructors, add them to table
        case (N.CaseClassDef(name, fields, parent), mod) => 
          table.getType(mod, parent) match {
            case Some(id) =>
              val sFields : List[S.Type]= fields.map(transformType(_, mod))
              table.addConstructor(mod, name, sFields, id)
            case None =>
              fatal(s"Parent name not valid in case class definition $name", d._1.position)
          }
        // Step 5: Discover functions signatures, add them to table
        case (N.FunDef(name, params, retType, _), mod) =>
          val sArgs = params.map{x => transformType(x.tt, mod)}
          val sRet = transformType(retType, mod)
          table.addFunction(mod, name, sArgs, sRet)
      }
    }

    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions
    
    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case N.AbstractClassDef(name) =>
        val Some(t) = table.getType(module, name) 
        S.AbstractClassDef(t)
      case N.CaseClassDef(name, _, _) =>
        val N.CaseClassDef(_, fields, parent) = df
        val Some((sym, sig)) = table.getConstructor(module, name)
        val Some(t) = table.getType(module, parent)
        val sFields = fields.map(x => S.TypeTree(transformType(x, module)))
        S.CaseClassDef(sym, sFields, t)
      case fd: N.FunDef =>
        transformFunDef(fd, module)
    }}.setPos(df)

    def transformFunDef(fd: N.FunDef, module: String): S.FunDef = {
      val N.FunDef(name, params, retType, body) = fd
      val Some((sym, sig)) = table.getFunction(module, name)

      params.groupBy(_.name).foreach { case (name, ps) =>
        if (ps.size > 1) {
          fatal(s"Two parameters named $name in function ${fd.name}", fd)
        }
      }

      val paramNames = params.map(_.name)

      val newParams = params zip sig.argTypes map { case (pd@N.ParamDef(name, tt), tpe) =>
        val s = Identifier.fresh(name)
        S.ParamDef(s, S.TypeTree(tpe).setPos(tt)).setPos(pd)
      }

      val paramsMap = paramNames.zip(newParams.map(_.name)).toMap

      S.FunDef(
        sym,
        newParams,
        S.TypeTree(sig.retType).setPos(retType),
        transformExpr(body)(module, (paramsMap, Map()))
      ).setPos(fd)
    }

    // This function takes as implicit a pair of two maps:
    // The first is a map from names of parameters to their unique identifiers,
    // the second is similar for local variables.
    // Make sure to update them correctly if needed given the scoping rules of Amy
    def transformExpr(expr: N.Expr)
                     (implicit module: String, names: (Map[String, Identifier], Map[String, Identifier])): S.Expr = {
      val (params, locals) = names
      val res = expr match {
        case N.Match(scrut, cases) =>
          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = pat match {
            case N.WildcardPattern() => (S.WildcardPattern(), List())
            case N.IdPattern(name) => 
              if (params.contains(name) || locals.contains(name))
                fatal(s"Name $name not valid", expr.position)
              val id = Identifier.fresh(name)
              (S.IdPattern(id), List((name, id)))
            case N.LiteralPattern(lit) => 
              val sLit = lit match {
                case N.IntLiteral(v) => S.IntLiteral(v)
                case N.BooleanLiteral(v) => S.BooleanLiteral(v)
                case N.StringLiteral(v) => S.StringLiteral(v)
                case N.UnitLiteral() => S.UnitLiteral()
              }
              (S.LiteralPattern(sLit), List())
            case N.CaseClassPattern(constr, args) =>
              val name = constr.name
              table.getConstructor(module, name) match {
                case Some((t,sig)) => 
                  val (sArgs, l) = args.map(transformPattern).unzip
                  (S.CaseClassPattern(t, sArgs), l.flatten)
                case None =>
                  fatal(s"Constructor $name doesn't exist", expr.position)
              }
          }

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)
            ???  // TODO
          }

          S.Match(transformExpr(scrut), cases.map(transformCase))

        case _ =>
          ???  // TODO: Implement the rest of the cases
      }
      res.setPos(expr)
    }

    // Putting it all together to construct the final program for step 6.
    val newProgram = S.Program(
      p.modules map { case mod@N.ModuleDef(name, defs, optExpr) =>
        S.ModuleDef(
          table.getModule(name).get,
          defs map (transformDef(_, name)),
          optExpr map (transformExpr(_)(name, (Map(), Map())))
        ).setPos(mod)
      }
    ).setPos(p)

    (newProgram, table)

  }
}

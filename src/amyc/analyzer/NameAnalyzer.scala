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
    // Based on the premise that only AbstractClasses and CaseClasses
    // Generate new types

    p.modules.foreach {
      case module: N.ModuleDef => {
        val moduleDefNames = module.defs.groupBy(_.name);
        moduleDefNames.foreach{
          case (name, defs) => if (defs.size > 1) {
            fatal(s"Two definitions named $name in module ${module.name}", defs.head.position)
          }
        }
      }
    }



    // Step 3: Discover types and add them to symbol table
    p.modules.foreach(
      (m) => m.defs.foreach {
        case N.CaseClassDef(name, fields, parent) => table.addType(m.name, name)
        case N.AbstractClassDef(name) => table.addType(m.name, name)
        case _ => Unit
      }
    )

    // Step 4: Discover type constructors, add them to table
    p.modules.foreach(
      (m) => m.defs.foreach {
        case ccd@N.CaseClassDef(name, fields, parent) => {
          table.addConstructor(
            m.name,
            name,
            fields.map(transformType(_, m.name)),
            table.getType(m.name, parent).getOrElse(
              fatal(s"Parent class $parent doest not exist in module ${m.name}", ccd.position)
            )
          )
        }
        case _ => Unit
      }
    )

    // Step 5: Discover functions signatures, add them to table
    p.modules.foreach(
      (m) => m.defs.foreach {
        case fd@N.FunDef(name, params, retType, body) => {
          table.getConstructor(m.name, name) match {
            case None => Unit
            case Some(id) => fatal(s"Function $name cannot share a name with a class", fd.position)
          }
          table.addFunction(
            m.name,
            name,
            params.map((p: N.ParamDef) => transformType(p.tt, m.name)),
            transformType(retType, m.name)
          )
        }
        case _ => Unit
      }
    )
    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions

    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case N.AbstractClassDef(name) =>
        S.AbstractClassDef(table.getType(module, name).get).setPos(df)
      case N.CaseClassDef(name, params, parent) => {
        val Some((sym, sig)) = table.getConstructor(module, name)

        val classMembers = params.zip(sig.argTypes).map{
          case (tt, tpe) => S.TypeTree(tpe).setPos(tt.position)
        }

        S.CaseClassDef(
          sym,
          classMembers,
          table.getType(module, parent).get).setPos(df)
      }
      case fd: N.FunDef =>
        transformFunDef(fd, module).setPos(df)
    }}

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

      def newLocal(name: String) = {
        locals.get(name) match {
          case None => Identifier.fresh(name)
          case Some(otherLocal) => fatal(s"Variable name $name already used.")
        }
      }

      def getTypeFromQName(qName: N.QualifiedName) = {
          println(qName)
          println(module)
          val a = qName.module match {
            case None => {println("NOnish"); table.getType(module, qName.name)}
            case Some(otherModule) => table.getType(otherModule, qName.name)
          }
          a match {
            case None => println("NOnish 2")
            case Some(thing) => println(thing)
          }
          println(s"typeFromQname: $a")
          a
      }

      def getFuncFromQName(qName: N.QualifiedName) = qName.module match {
        case None => table.getFunction(module, qName.name)
        case Some(otherModule) => table.getFunction(otherModule, qName.name)
      }

      def transformLit[T](lit: N.Literal[T]): S.Literal[T] = lit match {
        case N.IntLiteral(value) => S.IntLiteral(value)
        case N.BooleanLiteral(value) => S.BooleanLiteral(value)
        case N.StringLiteral(value) => S.StringLiteral(value)
        case N.UnitLiteral() => S.UnitLiteral()
      }

      val res = expr match {
        case N.Match(scrut, cases) =>


          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = {table.print; pat match {
            case N.WildcardPattern() => (S.WildcardPattern(), Nil)
            case N.IdPattern(name) => {
              val s = newLocal(name)// Validity of name should be checked here
              (S.IdPattern(s), (name, s):: Nil)
            }
            case N.LiteralPattern(lit) => (S.LiteralPattern(transformLit(lit)), Nil)
            case ccp@N.CaseClassPattern(constr, args) =>
              val subLocals = args.map(transformPattern(_))
              // Uniqueness of names should be checked here
              // Warnings can also be thrown in case of shadowing
              val check = subLocals.flatMap(_._2).groupBy(_._1)
              check.foreach{
                case (name, pairs) => if (pairs.size > 1) fatal(s"Case class pattern uses the variable name $name more than once")
              }

              (
                S.CaseClassPattern(
                  table
                  .getConstructor(constr.module.getOrElse(module), constr.name)
                  .getOrElse(
                    fatal(s"Case Class ${constr.toString()} does not exist", ccp.position)
                  )._1,
                subLocals.map(_._1)), subLocals.flatMap(_._2)
              )
              // Check on the arguments that it matches the
              // constructor arugments
              // Given module here is the module of decleration??
          }}

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)
            S.MatchCase(newPat, transformExpr(rhs)(module, (params, locals ++ moreLocals.toMap)))
            // TODO Here is where I should check the shadowing of params
          }

          S.Match(transformExpr(scrut), cases.map(transformCase))

        case N.Plus(lhs, rhs) => S.Plus(transformExpr(lhs), transformExpr(rhs))
        case N.Minus(lhs, rhs) => S.Minus(transformExpr(lhs), transformExpr(rhs))
        case N.Times(lhs, rhs) => S.Times(transformExpr(lhs), transformExpr(rhs))
        case N.Div(lhs, rhs) => S.Div(transformExpr(lhs), transformExpr(rhs))
        case N.Mod(lhs, rhs) => S.Mod(transformExpr(lhs), transformExpr(rhs))
        case N.LessThan(lhs, rhs) => S.LessThan(transformExpr(lhs), transformExpr(rhs))
        case N.LessEquals(lhs, rhs) => S.LessEquals(transformExpr(lhs), transformExpr(rhs))
        case N.And(lhs, rhs) => S.And(transformExpr(lhs), transformExpr(rhs))
        case N.Or(lhs, rhs) => S.Or(transformExpr(lhs), transformExpr(rhs))
        case N.Equals(lhs, rhs) => S.Equals(transformExpr(lhs), transformExpr(rhs))
        case N.Concat(lhs, rhs) => S.Concat(transformExpr(lhs), transformExpr(rhs))

        case N.Not(e) => S.Not(transformExpr(e))
        case N.Neg(e) => S.Neg(transformExpr(e))

        case lit: N.Literal[Any] => transformLit(lit)

        case c@N.Call(qname, args) => {
          // Could be better written
          S.Call(
            table
            .getFunction(
              qname.module.getOrElse(module), qname.name
            )
            .getOrElse(
              table.getConstructor(
                qname.module.getOrElse(module), qname.name
              ).getOrElse(
                fatal(s"Function ${qname.name} does not exist", c.position)
              )
            )._1,
            args.map(transformExpr)
          )

        }


        case v@N.Variable(name) => {
          S.Variable(
            (locals ++ params)
            .getOrElse(
              name,
              fatal(s"Variable of name $name does not exist", v.position)
            )
          )
        }

        case N.Sequence(e1, e2) => S.Sequence(
          transformExpr(e1), transformExpr(e2)
        )
        case N.Ite(cond, thenn, elze) => S.Ite(
          transformExpr(cond),
          transformExpr(thenn),
          transformExpr(elze)
        )

        case N.Let(df, value, body) =>
          val s = newLocal(df.name)
          S.Let(
            S.ParamDef(s, S.TypeTree(transformType(df.tt, module))),
            transformExpr(value),
            transformExpr(body)(module, (params, locals ++ Map(df.name -> s)))
          )

        case N.Error(msg) => S.Error(transformExpr(msg))
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

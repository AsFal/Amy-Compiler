package amyc
package analyzer

import utils._
import ast.SymbolicTreeModule._
import ast.Identifier
import ConversionMapper._

// The type checker for Amy
// Takes a symbolic program and rejects it if it does not follow the Amy typing rules.
object TypeChecker extends Pipeline[(Program, SymbolTable), (Program, SymbolTable)] {

  def run(ctx: Context)(v: (Program, SymbolTable)): (Program, SymbolTable) = {
    import ctx.reporter._

    val (program, table) = v

    case class Constraint(found: Type, expected: Type, pos: Position, e: Option[Expr])

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
        List(Constraint(found, expected, e.position, Some(e)))
        // We need the e so that we can replace the correct node with the conversion call
        // upon reconstructing the tree
        // TODO refactor and remove need for position

      def boolBinaryOp(lhs: Expr, rhs: Expr, ooperandType: Option[Type]): List[Constraint] = {
        val operandType = ooperandType match {
          case None => TypeVariable.fresh()
          case Some(tpe) => tpe
        }
        genConstraints(lhs, operandType) ++
        genConstraints(rhs, operandType) ++
        topLevelConstraint(BooleanType)
        // Not sure about the ordering of this
      }

      def simpleBinaryOp(lhs: Expr, rhs: Expr, tpe: Type): List[Constraint] = {
        genConstraints(lhs, tpe) ++
        genConstraints(rhs, tpe) ++
        topLevelConstraint(tpe)
      }

      e match {
        // Literals
        case IntLiteral(_) => topLevelConstraint(IntType)
        case StringLiteral(_) => topLevelConstraint(StringType)
        case UnitLiteral() => topLevelConstraint(UnitType)
        case BooleanLiteral(_) => topLevelConstraint(BooleanType)

        case Variable(name) => {
          env.get(name) match {
            // Should never hit the None case, handled by name analysis
            case Some(tpe) => topLevelConstraint(tpe)
          }
        }

        // Binary Operations
        // HINT: Take care to implement the specified Amy semantics
        case Plus(lhs, rhs) => simpleBinaryOp(lhs, rhs, IntType)
        case Minus(lhs, rhs) => simpleBinaryOp(lhs, rhs, IntType)
        case Times(lhs, rhs) => simpleBinaryOp(lhs, rhs, IntType)
        case Div(lhs, rhs) => simpleBinaryOp(lhs, rhs, IntType)
        case Mod(lhs, rhs) => simpleBinaryOp(lhs, rhs, IntType)

        case LessThan(lhs, rhs) => boolBinaryOp(lhs, rhs, Some(IntType))
        case LessEquals(lhs, rhs) => boolBinaryOp(lhs, rhs, Some(IntType))
        case And(lhs, rhs) => boolBinaryOp(lhs, rhs, Some(BooleanType))
        case Or(lhs, rhs) => boolBinaryOp(lhs, rhs, Some(BooleanType))
        case Equals(lhs, rhs) => boolBinaryOp(lhs, rhs, None)

        case Concat(lhs, rhs) => simpleBinaryOp(lhs, rhs, StringType)

        case Not(e) =>
          genConstraints(e, BooleanType) ++ topLevelConstraint(BooleanType)
        case Neg(e) =>
          genConstraints(e, IntType) ++ topLevelConstraint(IntType)

        case Call(qname, args) => {
          table.getFunction(qname) match {
            case Some(funcSig) =>
              args.zip(funcSig.argTypes).flatMap{
                case (e, tpe) => genConstraints(e, tpe)
              } ++ topLevelConstraint(funcSig.retType)
            case None => table.getConstructor(qname) match {
              case Some(constrSig) =>
                args.zip(constrSig.argTypes).flatMap{
                  case (e, tpe) => genConstraints(e, tpe)
                } ++ topLevelConstraint(constrSig.retType)
            }
          }
        }
        case Sequence(e1, e2) => {
          val e2Type = TypeVariable.fresh()
          genConstraints(e1, TypeVariable.fresh()) ++ // QUESTION The actual E1 we don't actually care about
          genConstraints(e2, e2Type) ++
          topLevelConstraint(e2Type)
        }
        case Let(df, value, body) => {
          val ParamDef(name, tt) = df
          val bodyType = TypeVariable.fresh()
          genConstraints(value, tt.tpe) ++
          genConstraints(body, bodyType)(env ++ Map(name -> tt.tpe)) ++
          topLevelConstraint(bodyType)
        }
        case ite@Ite(cond, thenn, elze) => {
          val iteType = TypeVariable.fresh()
          genConstraints(cond, BooleanType) ++
          genConstraints(thenn, iteType) ++
          genConstraints(elze, iteType) ++
          topLevelConstraint(iteType)
        }

        // Does not add any top level constraint, QUESTION
        case Error(msg) => {
          genConstraints(msg, StringType)
        }

        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          val exprType = TypeVariable.fresh()
          def handlePattern(pat: Pattern, scrutExpected: Type):
            (List[Constraint], Map[Identifier, Type]) = pat match
          {
            case WildcardPattern() => (Nil, Map())
            case IdPattern(name) => (Nil, Map(name -> scrutExpected)) // Just adds a local, does not create a constraint
            case LiteralPattern(lit) => (genConstraints(lit, scrutExpected), Map())
            case CaseClassPattern(constr, args) => {
              table.getConstructor(constr) match {
                case Some(construtor) =>
                  val subPatterns = args.zip(construtor.argTypes).map{
                    case (pattern, tpe) => handlePattern(pattern, tpe)
                  }
                  (
                    subPatterns.flatMap(_._1)
                      :+ Constraint(construtor.retType, scrutExpected, pat.position, None),
                    subPatterns.foldLeft(Map[Identifier, Type]())((acc, subPattern) => acc ++ subPattern._2)
                  )
              }
            }
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            genConstraints(cse.expr, exprType)(env ++ moreEnv) ++ patConstraints
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++
          cases.flatMap(cse => handleCase(cse, st)) ++
          topLevelConstraint(exprType)
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

      constraints map { case Constraint(found, expected, pos, e) =>
        Constraint(subst(found, from, to), subst(expected, from, to), pos, e)
      }
    }



    // Solve the given set of typing constraints and
    //  call `typeError` if they are not satisfiable.
    // We consider a set of constraints to be satisfiable exactly if they unify.
    // TODO module is not actually a String
    // In the current mode, it should work
    // the conversions might just not be applied to the right location
    def solveConstraints(constraints: List[Constraint])(implicit module: String): List[Conversion] = {
      constraints match {
        case Nil => Nil
        case Constraint(found, expected, _, _) :: more if (found == expected)
          => solveConstraints(more) // Useless constraint if already equal
        case Constraint(found, expected, pos, eOp) :: more => expected match {
          case tve@TypeVariable(id) => solveConstraints(subst_*(more, id, found))// Eliminate
          case _ => found match {
            case tvf@TypeVariable(id) => solveConstraints(subst_*(more, id, expected))// Orient && Eliminate

            // This is the case where found and expected in the constraint are both
            // types and they do not match ... ie the conflict case
            case _ => {
              // Here we should check if there exists a conversion in the table
              // We also have to check if the constraint contains an expression
              // that can be modified
              {
                for {
                  e <- eOp
                  conversionSig <- table.getConversion(module, found, expected)
                  // Missing module information
                  // Need to find a way to get the moduling information here
                } yield (e, conversionSig)
              } match {
                case None => fatal(s"Expected type $expected, found $found instead", pos)
                // TODO making this function tail recursive would be better
                case Some((e, conversionSig)) => List(Conversion(e, conversionSig)) ++ solveConstraints(more)
              }
            }
          }
        }
      }
    }

    // Putting it all together to type-check each module's functions and main expression.
    // TODO Instead of module foreach, module AST get converted to mnew modules
    // with appropriate conversion nodes
    val newModules = program.modules.map { mod =>
      // Put function parameters to the symbol table, then typecheck them against the return type
      val newDefs = mod.defs.map { case FunDef(id, params, retType, body) =>
        val env = params.map{ case ParamDef(name, tt) => name -> tt.tpe }.toMap
        val conversions = solveConstraints(genConstraints(body, retType.tpe)(env))(mod.name.name) // Module information here
        FunDef(
          id, params, retType,
          ConversionMapper(table).setConversions(conversions).mapExpression(body))
        case other => other
      }

      // Type-check expression if present. We allow the result to be of an arbitrary type by
      // passing a fresh (and therefore unconstrained) type variable as the expected type.
      val tv = TypeVariable.fresh()
      val newOptExpr = mod.optExpr match {
        case None => None
        case Some(e) => Some(
          ConversionMapper(table).setConversions(
            solveConstraints(genConstraints(e, tv)(Map()))(mod.name.name))
          .mapExpression(e))
      }
      ModuleDef(mod.name, newDefs, newOptExpr)
    }

    // v
    (Program(newModules), table)

  }
}

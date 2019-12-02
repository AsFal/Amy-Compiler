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

      def boolBinaryOp(lhs: Expr, rhs: Expr): List[Constraint] = {
        val freshOperand = TypeVariable.fresh()
        genConstraints(lhs, freshOperand) ++
        genConstraints(rhs, freshOperand) ++
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
            // Should never hit the None cas, handled by name analysis
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

        case LessThan(lhs, rhs) => boolBinaryOp(lhs, rhs)
        case LessEquals(lhs, rhs) => boolBinaryOp(lhs, rhs)
        case And(lhs, rhs) => boolBinaryOp(lhs, rhs)
        case Or(lhs, rhs) => boolBinaryOp(lhs, rhs)
        case Equals(lhs, rhs) => boolBinaryOp(lhs, rhs)

        case Concat(lhs, rhs) => simpleBinaryOp(lhs, rhs, StringType)

        case Not(e) =>
          genConstraints(e, BooleanType) ++ topLevelConstraint(BooleanType)
        case Neg(e) =>
          genConstraints(e, IntType) ++ topLevelConstraint(BooleanType)

        case Call(qname, args) => {
          table.getFunction(qname) match {
            case Some(funcSig) =>
              args.zip(funcSig.argTypes).flatMap{
                case (e, tpe) => genConstraints(e, tpe)
              } ++ topLevelConstraint(funcSig.retType)
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
                    case (pattern, tpe) => handlePattern(pattern, tpe)}
                  (
                    subPatterns.flatMap(_._1)
                      :+ Constraint(construtor.retType, scrutExpected, pat.position),
                    subPatterns.foldLeft(Map[Identifier, Type]())((acc, subPattern) => acc ++ subPattern._2)
                  )
              }
            }
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            genConstraints(cse.expr, scrutExpected)(env ++ moreEnv)
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))
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
        case Constraint(found, expected, _) :: more if (found == expected) => solveConstraints(more)
        case Constraint(found, expected, pos) :: more => expected match {
          case tve@TypeVariable(id) => subst_*(more, id, found)// Eliminate
          case _ => found match {
            case tvf@TypeVariable(id) => subst_*(more, id, expected)// Orient && Eliminate
            case _ => fatal(s"Expected type $expected, found $found instead", pos)
            // Clash, equality would've been caught by case 2
          }
        }
          // HINT: You can use the `subst_*` helper above to replace a type variable
          //       by another type in your current set of constraints.
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

package amyc
package analyzer

import ast.SymbolicTreeModule._
import ast.Identifier
import utils._
import scala.collection.mutable.ListBuffer

case class Conversion(e: Expr, conversionSig: (Identifier, FunSig))

case class ConversionMapper(table: SymbolTable) {
  var conversions: ListBuffer[Conversion] = new ListBuffer[Conversion]();

  def setConversions(c: List[Conversion]) = {
    conversions = c.to[ListBuffer]
    this
  }

  def conZ(e: Expr): Expr = {
    conversions.find{
      case Conversion(eConversion, cSig) => eConversion == e
    } match {
      case None => e
      case sC@Some(Conversion(_, cSig)) => {
        conversions -= sC.get
        Call(cSig._1, List(e))
      }
    }
  }

  def ambiguousConversions(childExprs: List[Expr], previousConversion: Option[Type]): Boolean =
    childExprs match {
      case Call(id, _) :: xs => table.getConversion(id) match {
        case None => ambiguousConversions(xs, previousConversion)
        case Some(FunSig(_, thisTpe, _)) => previousConversion match {
          case None => ambiguousConversions(xs, Some(thisTpe))
          case Some(tpe) =>
            if (tpe == thisTpe)
              ambiguousConversions(xs, previousConversion)
            else
              true
        }
      }
      case Nil => false // Ctx error here instead
      case _ :: xs => ambiguousConversions(xs, previousConversion)
    }

  def mapExpression(e: Expr): Expr = e match {
    // Huge switch case to propogate the convert function down
    // If the first level of two child branches changes
    // And the behaviour fo that node was relative, than an error ensues
    // TODO A quick way to check if both children are conversions
    case Plus(lhs, rhs) => Plus(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case Minus(lhs, rhs) => Minus(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case Times(lhs, rhs) => Times(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case Div(lhs, rhs) => Div(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case Mod(lhs, rhs) => Mod(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case LessThan(lhs, rhs) => LessThan(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case LessEquals(lhs, rhs) => LessEquals(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case And(lhs, rhs) => And(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case Or(lhs, rhs) => Or(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))
    case Concat(lhs, rhs) => Concat(mapExpression(conZ(lhs)), mapExpression(conZ(rhs)))

    case Equals(lhs, rhs) => {
      val l = List(lhs, rhs).map((c) => mapExpression(conZ(c)))
      ambiguousConversions(l, None)
      Equals(l(0), l(1))
    }

    case Not(e) => Not(mapExpression(conZ(e)))
    case Neg(e) => Neg(mapExpression(conZ(e)))

    case Call(qname, args) => Call(qname, args.map((c) => mapExpression(conZ(c))))
    case Sequence(e1, e2) => Sequence(mapExpression(e1), mapExpression(conZ(e2)))
    case Let(df, value, body) => Let(df, value, mapExpression(conZ(body)))

    case Ite(cond, thenn, elze) => {
      val l = List(thenn, elze).map((c) => mapExpression(conZ(c)))
      ambiguousConversions(l, None)
      Equals(l(0), l(1))
    }
    case Match(scrut, cases) => {
      val l = cases.map((c) => mapExpression(conZ(c.expr)))
      ambiguousConversions(l, None)
      Match(
        mapExpression(conZ(scrut)),
        cases.map{
          case MatchCase(pattern, e) => MatchCase(pattern, mapExpression(conZ(e)))
        }
      )
    }
    case Error(msg) => Error(mapExpression(conZ(msg)))

    case other => conZ(other)
  }
}

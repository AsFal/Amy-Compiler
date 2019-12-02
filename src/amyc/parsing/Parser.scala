package amyc
package parsing

import scala.language.implicitConversions

import amyc.ast.NominalTreeModule._
import amyc.utils._
import Tokens._
import TokenKinds._

import scallion.syntactic._
import java.util.function.BinaryOperator

// The parser for Amy
object Parser extends Pipeline[Iterator[Token], Program]
                 with Syntaxes[Token, TokenKind] with Debug[Token, TokenKind]
                 with Operators {
  import Implicits._

  override def getKind(token: Token): TokenKind = TokenKind.of(token)

  val eof: Syntax[Token] = elem(EOFKind)
  def op(string: String): Syntax[String] = accept(OperatorKind(string)) { case OperatorToken(name) => name }
  def kw(string: String): Syntax[Token] = elem(KeywordKind(string))

  implicit def delimiter(string: String): Syntax[Token] = elem(DelimiterKind(string))

  // An entire program (the starting rule for any Amy file).
  lazy val program: Syntax[Program] = many1(many1(module) ~<~ eof).map(ms => Program(ms.flatten.toList).setPos(ms.head.head))

  // A module (i.e., a collection of definitions and an initializer expression)
  lazy val module: Syntax[ModuleDef] = (kw("object") ~ identifier ~ "{" ~ many(definition) ~ opt(expr) ~ "}").map {
    case obj ~ id ~ _ ~ defs ~ body ~ _ => ModuleDef(id, defs.toList, body).setPos(obj)
  }

  // An identifier.
  val identifier: Syntax[String] = accept(IdentifierKind) {
    case IdentifierToken(name) => name
  }

  // An identifier along with its position.
  val identifierPos: Syntax[(String, Position)] = accept(IdentifierKind) {
    case id@IdentifierToken(name) => (name, id.position)
  }

  // A definition within a module.
  lazy val definition: Syntax[ClassOrFunDef] =
    functionDefinition | abstractClassDefinition | classDefinition

  lazy val functionDefinition: Syntax[ClassOrFunDef] =
    (kw("def")
    ~ identifier ~ delimiter("(").skip ~ parameters ~ delimiter(")").skip
    ~ delimiter(":").skip ~ typeTree ~ delimiter("=").skip
    ~ delimiter("{").skip ~ expr ~ delimiter("}").skip
    ).map{
      case df ~ name ~ params ~ retType ~ body => FunDef(name, params, retType, body).setPos(df)
    }

  lazy val abstractClassDefinition: Syntax[ClassOrFunDef] =
    (kw("abstract") ~ kw("class").skip ~ identifier).map{
      case abstrakt ~ name => AbstractClassDef(name).setPos(abstrakt)
    }

  lazy val classDefinition: Syntax[ClassOrFunDef] =
    (kw("case") ~ kw("class").skip ~ identifier
    ~ delimiter("(").skip ~ parameters ~ delimiter(")").skip
    ~ kw("extends").skip ~ identifier).map{
      case cse ~ name ~ params ~ parent => CaseClassDef(name, params.map(_.tt), parent).setPos(cse)
    }


  // A list of parameter definitions.
  lazy val parameters: Syntax[List[ParamDef]] = repsep(parameter, ",").map(_.toList)

  // A parameter definition, i.e., an identifier along with the expected type.
  lazy val parameter: Syntax[ParamDef] = (identifierPos ~ delimiter(":").skip ~ typeTree).map{
    case (name, pos) ~ paramType => ParamDef(name, paramType).setPos(pos)
  }

  // A type expression.
  lazy val typeTree: Syntax[TypeTree] = primitiveType | identifierType

  // A built-in type (such as `Int`).
  val primitiveType: Syntax[TypeTree] = accept(PrimTypeKind) {
    case tk@PrimTypeToken(name) => TypeTree(name match {
      case "Unit" => UnitType
      case "Boolean" => BooleanType
      case "Int" => IntType
      case "String" => StringType
      case _ => throw new java.lang.Error("Unexpected primitive type name: " + name)
    }).setPos(tk)
  }

  // A user-defined type (such as `List`).
  lazy val identifierType: Syntax[TypeTree] = qualifiedName.map((qn) => TypeTree(ClassType(qn._1)))

  // An expression.
  // HINT: You can use `operators` to take care of associativity and precedence
  lazy val expr: Syntax[Expr] = recursive{
    sequenceOrMatch | assignment
  }

  lazy val sequenceOrMatch: Syntax[Expr] = recursive{
    (subExpression ~
      (
        opt(
          delimiter(";").skip ~ expr |
          patternMatch.up[Expr]
        )
      )
    )
    .map{
      case (e1: Expr) ~ None => e1
      case (e1: Expr) ~ Some(Match(_, cases)) => Match(e1, cases).setPos(e1)
      case (e1: Expr) ~ Some((e2: Expr)) => Sequence(e1, e2).setPos(e1)
    }
  }

  lazy val patternMatch: Syntax[Match] = recursive {
    (kw("match") ~ delimiter("{").skip ~ many1(matchCase) ~ delimiter("}").skip).map{
      case mtch ~ cases => Match(Variable("temp"), cases.toList).setPos(mtch)
    }
  }

  lazy val assignment: Syntax[Expr] = recursive{
    (kw("val") ~ parameter ~ delimiter("=").skip ~ subExpression ~ delimiter(";").skip ~ expr).map{
      case valerianClerc ~ on ~ that ~ body => Let(on, that, body).setPos(valerianClerc.position)
    }
  }

  lazy val subExpression: Syntax[Expr] = recursive {
    operators(simpleExpr)( // expr here causes about 10 conflicts
      op("/") | op("*") is LeftAssociative,
      op("%") is LeftAssociative,
      op("+") | op("-") is LeftAssociative, // check waht these mean
      op("<=") | op("<") is LeftAssociative,
      op("&&") | op("||") | op("==") | op("++") is LeftAssociative
    ){
      case (l, "+", r) => Plus(l, r).setPos(l.position)
      case (l, "-", r) => Minus(l, r).setPos(l.position)
      case (l, "*", r) => Times(l, r).setPos(l.position)
      case (l, "/", r) => Div(l, r).setPos(l.position)
      case (l, "%", r) => Mod(l, r).setPos(l.position)
      case (l, "<", r) => LessThan(l, r).setPos(l.position)
      case (l, "<=", r) => LessEquals(l, r).setPos(l.position)
      case (l, "&&", r) => And(l, r).setPos(l.position)
      case (l, "||", r) => Or(l, r).setPos(l.position)
      case (l, "==", r) => Equals(l, r).setPos(l.position)
      case (l, "++", r) => Concat(l, r).setPos(l.position)
    } |
    (op("-").skip ~ subExpression).map{case operand => Neg(operand).setPos(operand.position)} |
    (op("!").skip ~ subExpression).map{case operand => Not(operand).setPos(operand.position)} |
    ifelse |
    error
  }

  lazy val ifelse: Syntax[Expr] = recursive{
    (kw("if") ~ delimiter("(").skip ~ subExpression ~ delimiter(")").skip ~
    delimiter("{").skip ~ expr ~ delimiter("}").skip ~
    kw("else").skip ~ delimiter("{").skip ~ expr ~ delimiter("}").skip).map{
      case iff ~ cond ~ ifValue ~ elseValue => Ite(cond, ifValue, elseValue).setPos(iff)
    }
  }

  lazy val error: Syntax[Expr] = recursive{
    (kw("error") ~ delimiter("(").skip ~ subExpression ~ delimiter(")").skip).map{
      case err ~ message => Error(message).setPos(err)
    }
  }

  // A literal expression.
  lazy val literal: Syntax[Literal[_]] = accept(LiteralKind) {
    case slt@StringLitToken(w) => StringLiteral(w).setPos(slt.position)
    case subwayBlt@BoolLitToken(b) => BooleanLiteral(b).setPos(subwayBlt.position)
    case ilt@IntLitToken(i) => IntLiteral(i).setPos(ilt.position)
  }


  lazy val matchCase: Syntax[MatchCase] = recursive {
    (kw("case") ~ pattern ~ delimiter("=>").skip ~ expr).map{
      case cse ~ p ~ e => MatchCase(p, e).setPos(cse.position)
    }
  }

  lazy val pattern: Syntax[Pattern] = recursive {
    literalPattern | wildPattern | idOrCaseClassPattern
  }

  lazy val literalPattern: Syntax[Pattern] = literal.map(lit => LiteralPattern(lit).setPos(lit.position)).up[Pattern]
  lazy val wildPattern: Syntax[Pattern] = kw("_").map((whatever) => WildcardPattern().setPos(whatever.position)).up[Pattern]
  lazy val idOrCaseClassPattern: Syntax[Pattern] =
    (qualifiedName ~ opt(delimiter("(").skip ~ repsep(pattern, ",") ~ delimiter(")").skip)).map{
      case (qName, pos) ~ None => IdPattern(qName.name).setPos(pos)
      case (qName, pos) ~ Some(otherPatterns) => CaseClassPattern(qName, otherPatterns.toList).setPos(pos)
    }

  // HINT: It is useful to have a restricted set of expressions that don't include any more operators on the outer level.
  lazy val simpleExpr: Syntax[Expr] = literal.up[Expr] | variableOrCall // | ???

  // lazy val variableOrCall: Syntax[Expr] = identifier.map{case name => Variable(name)}.up[Expr] | functionCall.up[Expr]

  lazy val variableOrCall: Syntax[Expr] = (qualifiedName ~ opt(functionArguments)).map{
    case (qName, pos) ~ None => Variable(qName.name).setPos(pos)
    case (qName, pos) ~ Some(args) => Call(qName, args).setPos(pos)
  }

  lazy val functionArguments: Syntax[List[Expr]] = recursive {
    (delimiter("(").skip ~ repsep(expr, ",") ~ delimiter(")").skip).map{
      case args => args.toList
    }
  }

  lazy val qualifiedName: Syntax[(QualifiedName, Position)] = (rep1sep(identifierPos, delimiter("."))).map{
    (seq: Seq[(String, Position)]) =>
      (
        if (seq.length == 1) QualifiedName(None, seq.last._1)
        else QualifiedName(Some(seq.take(seq.length - 1).map(_._1).mkString(".")), seq.last._1),
        seq.head._2
      )
  }

  // Ensures the grammar is in LL(1), otherwise prints some counterexamples
  lazy val checkLL1: Boolean = {
    if (program.isLL1) {
      true
    } else {
      debug(program)
      false
    }
  }

  override def run(ctx: Context)(tokens: Iterator[Token]): Program = {
    import ctx.reporter._
    if (!checkLL1) {
      ctx.reporter.fatal("Program grammar is not LL1!")
    }

    program(tokens) match {
      case Parsed(result, rest) => result
      case UnexpectedEnd(rest) => fatal("Unexpected end of input.")
      case UnexpectedToken(token, rest) => fatal("Unexpected token: " + token + ", possible kinds: " + rest.first.map(_.toString).mkString(", "))
    }
  }
}

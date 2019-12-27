package amyc.analyzer

import amyc.ast.Identifier
import amyc.ast.SymbolicTreeModule._
import amyc.utils.UniqueCounter

import scala.collection.mutable.HashMap

trait Signature[RT <: Type]{
  val argTypes: List[Type]
  val retType: RT
}
// The signature of a function in the symbol table
case class FunSig(argTypes: List[Type], retType: Type, owner: Identifier) extends Signature[Type]
// The signature of a constructor in the symbol table
case class ConstrSig(argTypes: List[Type], parent: Identifier, index: Int) extends Signature[ClassType] {
  val retType = ClassType(parent)
}

// A class that represents a dictionary of symbols for an Amy program
class SymbolTable {
// All these should be private
  val defsByName = HashMap[(String, String), Identifier]()
  val conversions = HashMap[(String, Type, Type), Identifier]()

  val modules = HashMap[String, Identifier]()

  val types = HashMap[Identifier, Identifier]()
  val functions = HashMap[Identifier, FunSig]()
  val constructors = HashMap[Identifier, ConstrSig]()

  val typesToConstructors = HashMap[Identifier, List[Identifier]]()

  val constrIndexes = new UniqueCounter[Identifier]

  def addModule(name: String) = {
    val s = Identifier.fresh(name)
    modules += name -> s
    s
  }
  def getModule(name: String) = modules.get(name)

  def addType(owner: String, name: String) = {
    val s = Identifier.fresh(name)
    defsByName += (owner, name) -> s
    types += (s -> modules.getOrElse(owner, sys.error(s"Module $name not found!")))
    s
  }
  def getType(owner: String, name: String) =
    defsByName.get(owner,name) filter types.contains
  def getType(symbol: Identifier) = types.get(symbol)

  def addConstructor(owner: String, name: String, argTypes: List[Type], parent: Identifier) = {
    val s = Identifier.fresh(name)
    defsByName += (owner, name) -> s
    constructors += s -> ConstrSig(
      argTypes,
      parent,
      constrIndexes.next(parent)
    )
    typesToConstructors += parent -> (typesToConstructors.getOrElse(parent, Nil) :+ s)
    s
  }
  def getConstructor(owner: String, name: String): Option[(Identifier, ConstrSig)] = {
    for {
      sym <- defsByName.get(owner, name)
      sig <- constructors.get(sym)
    } yield (sym, sig)
  }
  def getConstructor(symbol: Identifier) = constructors.get(symbol)

  def getConstructorsForType(t: Identifier) = typesToConstructors.get(t)

  def addFunction(owner: String, name: String, argTypes: List[Type], retType: Type) = {
    val s = Identifier.fresh(name)
    defsByName += (owner, name) -> s
    functions += s -> FunSig(argTypes, retType, getModule(owner).getOrElse(sys.error(s"Module $owner not found!")))
    s
  }
  def getFunction(owner: String, name: String): Option[(Identifier, FunSig)] = {
    for {
      sym <- defsByName.get(owner, name)
      sig <- functions.get(sym)
    } yield (sym, sig)
  }
  def getFunction(symbol: Identifier) = functions.get(symbol)

  def addConversion(owner: String, name: String, argTypes: List[Type], retType: Type) = {
    val s = addFunction(owner, name, argTypes, retType)
    val from = argTypes(0)
    val to = retType
    conversions += (owner, from, to) -> s
    s
  }

  def getconversion(symbol: Identifier) = functions.get(symbol)

  def getConversion(owner: String, from: Type, to: Type): Option[(Identifier, FunSig)] = {
    for {
      sym <- conversions.get(owner, from, to)
      sig <- functions.get(sym)
    } yield (sym, sig)
  }

  def toStringO =
    s"Defs by name: \n${defsByName.toString()}\n" +
    s"Modules: \n${modules.toString()}\n" +
    s"types: \n${types.toString()}\n" +
    s"Functions: \n${functions.toString()}\n" +
    s"Constructors: \n${constructors.toString()}\n" +
    s"Type to Constructors: \n${typesToConstructors.toString()}\n" +
    s"Constructor Indexes: \n${constrIndexes.toString()}\n"

  def print = println(toStringO)
}

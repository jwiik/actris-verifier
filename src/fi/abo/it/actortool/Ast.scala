package fi.abo.it.actortool

import scala.util.parsing.input.Positional

trait ASTNode extends Positional

sealed abstract class Actor(val id: String, val inports: List[InPort], 
    val outports: List[OutPort], val members: List[Member]) extends ASTNode {
  
  def isNetwork: Boolean = false
  def isActor: Boolean = false
  
  def fullName: String = id
  
  def hasInport(id: String) = inports.exists(p => p.portId == id)
  def hasOutport(id: String) = outports.exists(p => p.portId == id)
  def getInport(id: String) = inports.find(p => p.portId == id)
  def getOutport(id: String) = outports.find(p => p.portId == id)
}

sealed case class BasicActor(override val id: String, override val inports: List[InPort], 
    override val outports: List[OutPort], override val members: List[Member]) extends Actor(id,inports,outports,members) {
  override def isActor = true
  
  lazy val schedule = {
    val opt = members.find(m => m match {case sc: Schedule => true; case _ => false;})
    opt match {
      case Some(opt) => Some(opt.asInstanceOf[Schedule])
      case None => None
    }
  }
}

sealed case class Network(
    override val id: String, 
    override val inports: List[InPort], 
    override val outports: List[OutPort], 
    override val members: List[Member]) extends Actor(id,inports,outports,members) {
  
  override def isNetwork = true
  
  private lazy val userDefinedChannelInvariants = 
    for (m <- members.filter{ x => x.isChannelInvariant}) yield { m.asInstanceOf[ChannelInvariant] }
  private var inferredChannelInvariants: List[ChannelInvariant] = Nil
  
  def channelInvariants = inferredChannelInvariants:::userDefinedChannelInvariants
  
  def addChannelInvariant(chi: ChannelInvariant) { 
    inferredChannelInvariants = chi::inferredChannelInvariants 
  }
  
  private lazy val entities: List[Instance] = {
    members.find { x => x.isEntities } match {
      case None => Nil
      case Some(insts) => insts.asInstanceOf[Entities].entities
    }
  }
  
}

sealed abstract class Member extends ASTNode {
  def isDeclaration = false
  def isAction = false
  def isFSM = false
  def isPriority = false
  def isActorInvariant = false
  def isChannelInvariant = false
  def isEntities = false
  def isStructure = false
  def isSchedule = false
}

object Count {
  private var i = -1
  def next = { i = i+1; i }
  def reset = {i = -1}
}

sealed case class Action(
    private val label: Option[String], val init: Boolean, 
    val inputPattern: List[InputPattern], val outputPattern: List[OutputPattern],
    val guard: Option[Expr], 
    val requires: List[Expr], val ensures: List[Expr], varDecls: List[Declaration],
    val body: Option[List[Stmt]]) extends Member {

  var transitions: List[(String,String)] = Nil
  
  override def isAction = true
  
  def getInputCount(portId: String) = inputPattern.find(p => p.portId == portId) match {
    case None => 0
    case Some(i) => i.vars.size
  }
  
  def getOutputCount(portId: String) = outputPattern.find(p => p.portId == portId) match {
    case None => 0
    case Some(i) => i.exps.size
  }
  
  val fullName = label match { case Some(l) => l; case None => "anon$"+Count.next}
}

sealed case class Declaration(val id: String, val typ: Type, val constant: Boolean) extends Member {
  override def isDeclaration = true
}

sealed case class ActorInvariant(val expr: Expr, val generated: Boolean) extends Member {
  override def isActorInvariant = true
}

sealed case class ChannelInvariant(val expr: Expr, val generated: Boolean) extends Member {
  override def isChannelInvariant = true
}

sealed case class Entities(val entities: List[Instance]) extends Member {
  override def isEntities = true
}

sealed case class Structure(val connections: List[Connection]) extends Member {
  override def isStructure = true
}

sealed case class Schedule(val initState: String, val transitions: List[Transition]) extends Member {
  override def isSchedule = true
  lazy val states = {
    (for (t <- transitions) yield List(t.from,t.to)).flatten.distinct
  }
  
  def transitionsOnAction(action: String) = {
    for (t <- transitions.filter(t => t.action == action)) yield (t.from,t.to)
  }
}

sealed case class Instance(val id: String, val actorId: String, val parameters: List[Expr]) extends ASTNode {
  var actor: Actor = null
}

sealed case class Connection(val id: String, val from: PortRef, val to: PortRef) extends ASTNode {
  var typ: Type = null
}

sealed case class Transition(action: String, from: String, to: String) extends ASTNode

sealed case class PortRef(val actor: Option[String], val name: String) extends ASTNode

sealed abstract class Port(val id: String, val portType: Type) extends ASTNode {
  def inPort = false
  def outPort = false
}

sealed case class InPort(val portId: String, override val portType: Type) extends Port(portId,portType) {
  override def inPort = true
}

sealed case class OutPort(val portId: String, override val portType: Type) extends Port(portId,portType) {
  override def outPort = true
}

sealed abstract class Pattern(val portId: String) extends ASTNode

sealed case class InputPattern(override val portId: String, val vars: List[Id]) extends Pattern(portId) {
  def numConsumed = vars.size
}
sealed case class OutputPattern(override val portId: String, val exps: List[Expr]) extends Pattern(portId) {
  def numProduced = exps.size
}

sealed abstract class Expr extends ASTNode {
  var typ: Type = null
}
sealed case class UnMinus(val exp: Expr) extends Expr {
  val operator = "-"
}

sealed case class Not(val exp: Expr) extends Expr

sealed abstract class BinaryExpr(val left: Expr, val right: Expr) extends Expr {
  val operator: String
}

sealed case class Or(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "||"
}
sealed case class And(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "&&"
}
sealed case class Implies(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "==>"
}
sealed case class Iff(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "<==>"
}
sealed case class Plus(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "+"
}
sealed case class Minus(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "-"
}
sealed case class Times(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "*"
}
sealed case class Div(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "/"
}
sealed case class Mod(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "%"
}
sealed case class Eq(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "="
}
sealed case class NotEq(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "!="
}
sealed case class Greater(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = ">"
}
sealed case class Less(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "<"
}
sealed case class AtLeast(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = ">="
}
sealed case class AtMost(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "<="
}
sealed case class IfThenElse(val cond: Expr, val thenExpr: Expr, val elseExpr: Expr) extends Expr

sealed abstract class Quantifier(val vars: List[Declaration], val expr: Expr, val pattern: Option[Expr]) extends Expr {
  val operator: String
}

sealed case class Forall(
    override val vars: List[Declaration], override val expr: Expr, override val pattern: Option[Expr]) extends Quantifier(vars,expr,pattern) {
  override val operator = "forall"
}

sealed case class Exists(
    override val vars: List[Declaration], override val expr: Expr, override val pattern: Option[Expr]) extends Quantifier(vars,expr,pattern) {
  override val operator = "exists"
}

sealed abstract class SuffixedExpr(val exp: Expr) extends Expr
case class IndexAccessor(override val exp: Expr, val suffix: Expr) extends SuffixedExpr(exp)

sealed case class FunctionApp(val name: String, val parameters: List[Expr]) extends Expr

sealed abstract class Assignable extends Expr
sealed case class Id(val id: String) extends Assignable
sealed abstract class Literal extends Expr
sealed case class IntLiteral(val value: Int) extends Literal
sealed case class BoolLiteral(val value: Boolean) extends Literal
sealed case class FloatLiteral(val value: String) extends Literal

sealed case class IndexSymbol(id: String) extends Expr {
  var indexedExpr: Expr = null
}

sealed abstract class Stmt extends ASTNode
sealed case class Assignment(val asgn: Assignable, val expr: Expr) extends Stmt
sealed case class IfElse(val ifCond: Expr, val ifStmt: List[Stmt], val elseIfs: List[ElseIf], val elseStmt: List[Stmt]) extends Stmt
sealed case class ElseIf(val cond: Expr, val stmt: List[Stmt])
sealed case class While(val cond: Expr, val invariants: List[Expr], val stmt: List[Stmt]) extends Stmt
sealed case class Assert(val cond: Expr) extends Stmt
sealed case class Assume(val cond: Expr) extends Stmt
sealed case class Havoc(val vars: List[Id]) extends Stmt



sealed abstract class Type(val id: String) extends ASTNode {
  def isPrimitive = false
  def isParametrized = false
  def isNumeric = false
  def isInt = false
  def isUint = false
  def isBool = false
  def isFloat = false
  def isHalf = false
  def isUnknown = false
  def isChannel = false
  def isIndexed = false
  def isActor = false
}

sealed abstract class ParamType(val name: String, parameters: List[Type]) extends Type(name) {
  override def isParametrized = true
}
sealed abstract class IndexedType(override val name: String, val resultType: Type, val indexType: Type) extends 
  ParamType(name,List(resultType,indexType)) {
  override def isIndexed = true
}
  
sealed case class IntType(size: Int) extends Type("int") {
  override def isInt = true
  override def isNumeric = true
}
sealed case class UintType(size: Int) extends Type("uint") {
  override def isInt = true
  override def isNumeric = true
}
case object BoolType extends Type("bool") {
  override def isBool = true
}
case object FloatType extends Type("float") {
  override def isFloat = true
  override def isNumeric = true
}
case object HalfType extends Type("half") {
  override def isHalf = true
  override def isNumeric = true
}
case object UnknownType extends Type("unknown") {
  override def isHalf = true
  override def isNumeric = true
}
case class ChanType(contentType: Type) extends IndexedType("Chan",contentType,IntType(32)) {
  override def isChannel = true
}
case class ActorType(actor: Actor) extends Type("actor") {
  override def isActor = true
}

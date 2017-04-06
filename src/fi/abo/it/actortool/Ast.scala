package fi.abo.it.actortool

import scala.util.parsing.input.Positional
import scala.util.parsing.input.Position

trait FilePosition extends Position {
  def fileName: Option[String]
  def lineContents = null
  override def toString = fileName match {
    case Some(file) => file + "(" + line + "." + column  + ")"
    case None => "<unknown_file>(" + line + "." + column  + ")"
  }
}

case class ConcretePosition(
    override val fileName: Option[String], 
    override val line: Int, 
    override val column: Int) extends FilePosition

object NoFilePosition extends FilePosition {
  def fileName = None
  def line = -1
  def column = -1
}

trait ASTNode {
  val annotations: List[Annotation] = Nil
  def hasAnnotation(name: String) = annotations.exists { a => a.name == name }
  private var _pos: FilePosition = NoFilePosition 
  def pos: FilePosition = _pos
  def setPos(newPos: FilePosition): this.type = { _pos = newPos; this }
  def setPos(fileName: Option[String], newPos: Position): this.type = { 
    _pos = ConcretePosition(fileName, newPos.line, newPos.column); 
    this 
  }
  
}

sealed abstract class TopDecl(val id: String) extends ASTNode {
  def isNetwork: Boolean = false
  def isActor: Boolean = false
  def isUnit: Boolean = false
  def isType: Boolean = false
}

sealed case class Annotation(name: String) extends ASTNode

sealed case class TypeDecl(tp: RefType, fields: List[Declaration]) extends TopDecl(tp.id)

sealed case class DataUnit(
    override val id: String, 
    val constants: List[Declaration]) extends TopDecl(id) {
  override def isUnit = true
}

sealed abstract class DFActor(
    override val annotations: List[Annotation],
    override val id: String, val parameters: List[Declaration],
    val inports: List[InPort], val outports: List[OutPort], 
    val members: List[Member]) extends TopDecl(id) {
  
  def fullName: String = id
  
  private var _invariants: List[ActorInvariant] = 
    for (m <- members.filter{ x => x.isActorInvariant}) yield { m.asInstanceOf[ActorInvariant] }
  
  def actorInvariants = _invariants
  
  def addInvariant(invs: Expr, free: Boolean) { addInvariants(List(invs), free) }
  
  def addInvariants(invs: List[Expr], free: Boolean) {
    val newInvariants = invs map { x => ActorInvariant(Assertion(x,free),true,true) }
    _invariants = _invariants:::newInvariants
  }
  
  lazy val actions: List[Action] =
    members.filter { x => x.isAction } map { x => x.asInstanceOf[Action] }
  
  lazy val variables: List[Declaration] = 
    members.filter { x => x.isDeclaration } map { x => x.asInstanceOf[Declaration] }
  
//  lazy val actorInvariants: List[ActorInvariant] = {
//    members.filter { x => x.isActorInvariant } map { x => x.asInstanceOf[ActorInvariant] }
//  }
  
  lazy val streamInvariants = actorInvariants.filter { x => x.stream }
  
  lazy val schedule = {
    val opt = members.find(m => m match {case sc: Schedule => true; case _ => false;})
    opt match {
      case Some(opt) => Some(opt.asInstanceOf[Schedule])
      case None => None
    }
  }
  
  lazy val priority = {
    val opt = members.find(m => m match {case pr: Priority => true; case _ => false;})
    opt match {
      case Some(opt) => Some(opt.asInstanceOf[Priority])
      case None => None
    }
  }
  
  def hasInport(id: String) = inports.exists(p => p.id == id)
  def hasOutport(id: String) = outports.exists(p => p.id == id)
  def getInport(id: String) = inports.find(p => p.id == id)
  def getOutport(id: String) = outports.find(p => p.id == id)
}

sealed case class BasicActor(
    override val annotations: List[Annotation],
    override val id: String, override val parameters: List[Declaration], 
    override val inports: List[InPort], override val outports: List[OutPort], 
    override val members: List[Member]) 
    extends DFActor(annotations,id,parameters,inports,outports,members) {
  
  def getFunctionDecls = members.filter { x => x.isFunctionDecl } map { _.asInstanceOf[FunctionDecl] } 
  
  override def isActor = true
}

sealed case class Network(
    override val annotations: List[Annotation],
    override val id: String, 
    override val parameters: List[Declaration], 
    override val inports: List[InPort], 
    override val outports: List[OutPort], 
    override val members: List[Member]) extends DFActor(annotations,id,parameters,inports,outports,members) {
  
  override def isNetwork = true
  
  private var _channelInvariants: List[ChannelInvariant] = 
    for (m <- members.filter{ x => x.isChannelInvariant}) yield { m.asInstanceOf[ChannelInvariant] }
  
  def channelInvariants = {
    _channelInvariants
  }
  
  def addChannelInvariant(chi: Expr, free: Boolean) { addChannelInvariants(List(chi), free) }
  
  def addChannelInvariants(chis: List[Expr], free: Boolean) {
    val newInvariants = chis map { x => ChannelInvariant(Assertion(x,free),true) }
    _channelInvariants = _channelInvariants:::newInvariants
  }
  
  lazy val entities: Option[Entities] = {
    members.find { x => x.isEntities } match {
      case None => None
      case Some(insts) => Some(insts.asInstanceOf[Entities])
    }
  }
  
  lazy val structure: Option[Structure] = {
    members.find { x => x.isStructure } match {
      case None => None
      case Some(struct) => Some(struct.asInstanceOf[Structure])
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
  def isFunctionDecl = false
}

object Count {
  private var i = -1
  def next = { i = i+1; i }
  def reset = {i = -1}
}

object ActionClass extends Enumeration {
  type ActionClass = Value
  val Normal, Primary, Error, Recovery = Value
}

sealed case class Action(
    val label: Option[String], val aClass: ActionClass.Value, val init: Boolean, 
    val inputPattern: List[InputPattern], val outputPattern: List[OutputPattern],
    val guard: Option[Expr], 
    val requires: List[Expr], val ensures: List[Expr], variables: List[Declaration],
    val body: List[Stmt]) extends Member {
  
  override def isAction = true
  
  def portInputCount(portId: String) = portInputPattern(portId) match {
    case None => 0
    case Some(i) => i.vars.size
  }
  
  def portOutputCount(portId: String) = portOutputPattern(portId) match {
    case None => 0
    case Some(i) => i.exps.size
  }
  
  def portInputPattern(portId: String) = inputPattern.find(p => p.portId == portId)
  
  def portOutputPattern(portId: String) = outputPattern.find(p => p.portId == portId)
  
  val fullName = label.getOrElse("anon$"+Count.next)
}

sealed case class Declaration(val id: String, val typ: Type, 
    val constant: Boolean, val value: Option[Expr]) extends Member {
  override def isDeclaration = true
}

sealed case class Assertion(val expr: Expr, val free: Boolean, val msg: Option[String]) extends ASTNode {
  def this(expr: Expr, free: Boolean) = this(expr,free,None)
}

object Assertion {
  def apply(expr: Expr, free: Boolean) = new Assertion(expr,free,None)
}

sealed abstract class Invariant(val assertion: Assertion, val generated: Boolean) extends Member {
  def expr = assertion.expr
}

sealed case class ActorInvariant(
    override val assertion: Assertion, 
    override val generated: Boolean, 
    val stream: Boolean) extends Invariant(assertion,generated) {
  
  override def isActorInvariant = true
}

sealed case class ChannelInvariant(override val assertion: Assertion, override val generated: Boolean) extends Invariant(assertion,generated) {
  override def isChannelInvariant = true
}

sealed case class FunctionDecl(val name: String, val inputs: List[Declaration], val output: Type, val expr: Expr) extends Member {
  override def isFunctionDecl = true
}

sealed case class Entities(val entities: List[Instance]) extends Member {
  override def isEntities = true
}

sealed case class Structure(val connections: List[Connection]) extends Member {
  override def isStructure = true
  
  def getInputChannel(portId: String) = connections.find {
    x => x match {
      case Connection(_,PortRef(None,p),_,_) => p == portId
      case _ => false
    }
  }
  
  def getOutputChannel(portId: String) = connections.find {
    x => x match {
      case Connection(_,_,PortRef(None,p),_) => p == portId
      case _ => false
    }
  }
  
  def incomingConnection(entityId: String, portId: String) = connections.find { 
    x => x match {
      case Connection(_,_,PortRef(Some(e),p),_) => entityId == e && portId == p
      case _ => false
    } 
  }
  
  def outgoingConnections(entityId: String, portId: String) = {
    val cons = connections.find { 
      x => x match {
        case Connection(_,PortRef(Some(e),p),_,_) => entityId == e && portId == p
        case _ => false
      } 
    }
    cons
  }
  
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

sealed case class Priority(val orders: List[(Id,Id)]) extends Member

sealed case class Instance(
    val id: String, val actorId: String, val arguments: List[Expr], 
    override val annotations: List[Annotation]) extends ASTNode {

  var actor: DFActor = null
}

sealed case class Connection(
    val label: Option[String], val from: PortRef, val to: PortRef, 
    override val annotations: List[Annotation]) extends ASTNode {
  
  var typ: Type = null
  
  val id = label.getOrElse("anon$"+Count.next)
  
  def isInput = from match {
    case PortRef(None,_) => true
    case PortRef(Some(_),_) => false
  }
  
  def isOutput = to match {
    case PortRef(None,_) => true
    case PortRef(Some(_),_) => false
  }
}


sealed case class Transition(action: String, from: String, to: String) extends ASTNode

sealed case class PortRef(val actor: Option[String], val name: String) extends ASTNode

sealed abstract class Port(val id: String, val portType: Type) extends ASTNode {
  def inPort = false
  def outPort = false
}

sealed case class InPort(override val id: String, override val portType: Type) extends Port(id,portType) {
  override def inPort = true
}

sealed case class OutPort(override val id: String, override val portType: Type) extends Port(id,portType) {
  override def outPort = true
}

sealed abstract class Pattern(val portId: String, val list: List[Expr], val repeat: Int) extends ASTNode

sealed case class InputPattern(override val portId: String, val vars: List[Id], override val repeat: Int) extends Pattern(portId,vars,repeat) {
  def numConsumed = vars.size
}
sealed case class OutputPattern(override val portId: String, val exps: List[Expr], override val repeat: Int) extends Pattern(portId,exps,repeat) {
  def numProduced = exps.size
}

sealed abstract class Expr extends ASTNode {
  var typ: Type = null
}
sealed case class UnMinus(val exp: Expr) extends Expr {
  val operator = "-"
}

sealed case class Not(val exp: Expr) extends Expr

sealed case class BwNot(val exp: Expr) extends Expr {
  val operator = "~"
}

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
sealed case class RShift(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = ">>"
}
sealed case class LShift(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "<<"
}
sealed case class BwAnd(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "&"
}
sealed case class BwOr(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "|"
}
sealed case class BwXor(override val left: Expr, override val right: Expr) extends BinaryExpr(left,right) {
  override val operator = "^"
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
    override val vars: List[Declaration], override val expr: Expr, 
    override val pattern: Option[Expr]) extends Quantifier(vars,expr,pattern) {
  
  override val operator = "forall"

  def this(vars: List[Id], expr: Expr) = this(vars map {x => Declaration(x.id,x.typ,false,None)},expr,None)
  
}

object Forall {
  def apply(vars: List[Id], expr: Expr) = new Forall(vars,expr)
}


sealed case class Exists(
    override val vars: List[Declaration], override val expr: Expr, 
    override val pattern: Option[Expr]) extends Quantifier(vars,expr,pattern) {
  override val operator = "exists"
}

sealed abstract class Assignable extends Expr
sealed abstract class SuffixedExpr(val exp: Expr) extends Assignable
case class IndexAccessor(override val exp: Expr, val suffix: Expr) extends SuffixedExpr(exp)
case class FieldAccessor(override val exp: Expr, val suffix: String) extends SuffixedExpr(exp)

sealed case class FunctionApp(val name: String, val parameters: List[Expr]) extends Expr

sealed case class ListLiteral(val elements: List[Expr]) extends Expr
//sealed case class Range(val start: Int, val end: Int) extends Expr


sealed case class Id(val id: String) extends Assignable
sealed abstract class Literal extends Expr
sealed case class IntLiteral(val value: Int) extends Literal
sealed case class BoolLiteral(val value: Boolean) extends Literal
sealed case class FloatLiteral(val value: String) extends Literal
sealed case class HexLiteral(val value: String) extends Literal

sealed case class SpecialMarker(val value: String) extends Expr {
  private var data: Map[String,Object] = Map.empty
  
  def addExtraData(name: String, obj: Object) {
    data = data + (name -> obj)
  }
  def extraData: Map[String,Object] = data 
}

sealed abstract class Stmt extends ASTNode
sealed case class Assign(val id: Id, val expr: Expr) extends Stmt
sealed case class MapAssign(val id: Expr, val expr: Expr) extends Stmt
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
  def isUnsignedInt = false
  def isSignedInt = false
  def isBool = false
  def isFloat = false
  def isHalf = false
  def isUnknown = false
  def isChannel = false
  def isIndexed = false
  def isActor = false
  def isList = false
  def isRef = false
  def isBv = false
  def isMap = false
}

sealed case class RefType(val name: String) extends Type(name) {
  override def isRef = true
}

sealed abstract class ParamType(val name: String, parameters: List[Type]) extends Type(name) {
  override def isParametrized = true
}
sealed abstract class IndexedType(
    override val name: String, val resultType: Type, val indexType: Type) extends ParamType(name,List(resultType,indexType)) {
  
  override def isIndexed = true
}

sealed abstract class PrimitiveType(name: String) extends Type(name) 

sealed abstract class AbstractIntType(name: String, val size: Int) extends PrimitiveType(name+"("+size+")") {
  override def isInt = true
  override def isNumeric = true
  override def isBv = false
}

sealed case class IntType(override val size: Int) extends AbstractIntType("int", size) {
  override def isSignedInt = true
}

object IntType extends IntType(-1)

sealed case class UintType(override val size: Int) extends AbstractIntType("uint", size) {
  override def isUnsignedInt = true
}

object UintType extends UintType(-1)

case object BoolType extends PrimitiveType("bool") {
  override def isBool = true
}
case object FloatType extends PrimitiveType("float") {
  override def isFloat = true
  override def isNumeric = true
}
case object HalfType extends PrimitiveType("half") {
  override def isHalf = true
  override def isNumeric = true
}
case object UnknownType extends Type("unknown") {
  override def isHalf = true
  override def isNumeric = true
}
case class ChanType(contentType: Type) extends IndexedType("Chan",contentType,IntType(-1)) {
  override def isChannel = true
}
case class ActorType(actor: DFActor) extends Type("actor") {
  override def isActor = true
}
case class ListType(contentType: Type, val size: Int) extends IndexedType(
    "List("+contentType.id+","+size+")",contentType,IntType(-1)) {
  override def isList = true
}
case class MapType(val domainType: Type, val rangeType: Type) extends IndexedType("Map[" + domainType.id + "-->" + rangeType.id + "]", rangeType, domainType) {
  override def isMap = true
}
case class BvType(val size: Int) extends PrimitiveType("bv"+size) {
  override def isBv = true
}

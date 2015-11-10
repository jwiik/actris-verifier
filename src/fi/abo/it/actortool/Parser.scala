package fi.abo.it.actortool

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator._
import scala.util.parsing.input.PagedSeqReader
import scala.collection.immutable.PagedSeq
import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional
import scala.util.parsing.input.NoPosition
import java.io.File

import scala.language.postfixOps

class Parser extends StandardTokenParsers {
  
  def parseFile(file: File) = 
    phrase(programUnit)(new lexical.Scanner(new PagedSeqReader(PagedSeq fromFile file)))
  def Semi = ";" ?
  
  case class PositionedString(v: String) extends Positional
  
  lexical.reserved += ("actor", "network", "unit", "action", "true", "false", "null", "int", "bool", 
                       "guard", "entities", "structure", "int", "bool", "invariant", "chinvariant", 
                       "end", "forall", "exists", "do", "assert", "assume", "initialize", "requires",
                       "ensures", "var", "next", "last", "schedule", "fsm", "regexp"
                      )
  lexical.delimiters += ("(", ")", "<==>", "==>", "&&", "||", "==", "!=", "<", "<=", ">=", ">", "=",
                       "+", "-", "*", "/", "%", "!", ".", ";", ":", ":=", ",", "|", "[", "]", ":[",
                       "-->", "::", "{", "}", "<<" , ">>")
                       
  def programUnit = (actorDecl | networkDecl | unitDecl)*
  
  def unitDecl = positioned(("unit" ~> ident ~ (":" ~> (varDecl*)) <~ "end" ) ^^ {
    case (id ~ decls) => DataUnit(id,decls)
  })
  
  def actorDecl =
    positioned(("actor" ~> ident ~ ("(" ~> repsep(formalParam,",") <~ ")" ?) ~ repsep(inPortDecl,",") ~ 
        ("==>" ~> repsep(outPortDecl,",")) ~ (":" ~> (actorMember*)) <~ "end") ^^ {
      case (id ~ Some(params) ~ inports ~ outports ~ members) => BasicActor(id, params, inports, outports, members)
      case (id ~ None ~ inports ~ outports ~ members) => BasicActor(id, Nil, inports, outports, members)
    })
    
  def networkDecl =
    positioned(("network" ~> ident ~ ("(" ~> repsep(formalParam,",") <~ ")" ?) ~ repsep(inPortDecl,",") ~ 
        ("==>" ~> repsep(outPortDecl,",")) ~ (":" ~> (networkMember*)) <~ "end") ^^ {
      case (id ~ Some(params) ~ inports ~ outports ~ members) => Network(id, params, inports, outports, members)
      case (id ~ None ~ inports ~ outports ~ members) => Network(id, Nil, inports, outports, members)
    })
  
  def formalParam = positioned(
      (typeName ~ ident) ^^ {
        case (tName ~ id) => Declaration(id,tName,true)
      }  
    )
  def inPortDecl: Parser[InPort] = positioned((typeName ~ ident) ^^ {
    case (tName ~ id) => InPort(id,tName)
  })
  
  def outPortDecl: Parser[OutPort] = positioned((typeName ~ ident) ^^{
    case (tName ~ id) => OutPort(id,tName)
  })
  
  def actorMember: Parser[Member] = positioned(actorInvDecl | actionDecl | varDecl | scheduleBlock)
  
  def networkMember: Parser[Member] = positioned(
      actorInvDecl | chInvDecl | entitiesBlock | structureBlock | actionDecl)
  
  def entitiesBlock: Parser[Entities] = positioned(("entities" ~> repsep(entityDecl,Semi) <~ (Semi?) <~ "end") ^^ {
    case entities => Entities(entities)
  })
  
  def structureBlock: Parser[Structure] = positioned(("structure" ~> repsep(connection,Semi) <~ (Semi?) <~ "end") ^^ {
    case connections => Structure(connections)
  })
  
  
  
  def scheduleBlock: Parser[Schedule] = 
    positioned(("schedule" ~> "fsm" ~ ident ~ (":" ~> repsep(transition,Semi) <~ (Semi?) <~ "end")) ^^ {
      case  "fsm" ~ init ~ transitions => Schedule(init,transitions)
    })
  
  //def schedType = "fsm" | "regexp" 
  
  def entityDecl = positioned(ident ~ ("=" ~> (ident ~ paramList)) ^^ {
    case name ~ (actorId ~ params) => Instance(name,actorId,params)
  })
  
  def connection = positioned(ident ~ (":" ~> portRef ~ ("-->" ~> portRef)) ^^ {
    case id ~ (from ~ to) => Connection(id,from,to)
  })
  
  def transition = positioned(ident ~ ("(" ~> ident <~ ")") ~ ("-->" ~> ident) ^^ {
    case (from ~ act ~ to)  => Transition(act,from,to)
  })
  
  def paramList: Parser[List[Expr]] = ("(" ~> repsep(expression,",") <~ ")" ^^ {
    case exps => exps
  })
  
  def actorInvDecl = positioned(("invariant" ~> expression) ^^ {
    case expr => ActorInvariant(expr,false)
  })
  
  def chInvDecl = positioned(("chinvariant" ~> expression) ^^ {
    case expr => ChannelInvariant(expr,false)
  })
  
  def varDecl = positioned((typeName ~ ident <~ Semi) ^^ {
    case (typ ~ id) => Declaration(id,typ,false)
  })
   
  def actionDecl: Parser[Action] = positioned(
    (((ident <~ ":")?) ~ 
        ("action" | "initialize") ~ 
        repsep(inputPattern,",") ~ 
        ("==>" ~> repsep(outputPattern,",")) ~
        ("guard" ~> expression ?) ~
        ("requires" ~> expression *) ~
        ("ensures" ~> expression *) ~
        ("var" ~> repsep(varDecl,",") ?) ~
        ("do" ~> statementBody ?)
        <~ "end") ^^ {
      case (id ~ "action" ~ inputs ~ outputs ~ guard ~ requires ~ ensures ~ vars ~ stmt) => 
        Action(id,false,inputs,outputs,guard,requires,ensures,vars.getOrElse(Nil),stmt)
      case (id ~ "initialize" ~ inputs ~ outputs ~ guard ~ requires ~ ensures ~ vars ~ stmt) => 
        Action(id,true,inputs,outputs,guard,requires,ensures,vars.getOrElse(Nil),stmt)
    }
  )
  
  def inputPattern = positioned(ident ~ (":[" ~> repsep(identifier,",") <~ "]") ^^ {
    case (port ~ vars) => InputPattern(port, vars)
  })
  
  def outputPattern = positioned(ident ~ (":[" ~> repsep(expression,",") <~ "]") ^^ {
    case (port ~ exps) => OutputPattern(port, exps)
  })  

  
  def expression: Parser[Expr] = positioned(iffExpr) 
  
  def iffExpr: Parser[Expr] = positioned((implExpr ~ ("<==>" ~> iffExpr ?)) ^^ {
    case (e ~ None) => e
    case (e1 ~ Some(e2)) => Iff(e1,e2)
  })
  
  def implExpr: Parser[Expr] = positioned((logicalExpr ~ ("==>" ~> implExpr ?)) ^^ {
    case (e ~ None) => e
    case (e1 ~ Some(e2)) => Implies(e1,e2)
  })
  
  def logicalExpr: Parser[Expr] = positioned(cmpExpr ~ (( ("&&" ~ cmpExpr +) | ("||" ~ cmpExpr +) )?) ^^ {
    case e ~ None => e
    case e0 ~ Some(rest) => 
      (rest foldLeft e0) {
        case (a, "&&" ~ b) => And(a,b)
        case (a, "||" ~ b) => Or(a,b) 
      }
  })
  
  def cmpExpr: Parser[Expr] = positioned((bitManipExpr ~ ((cmpOp ~ bitManipExpr) ?)) ^^ {
    case e ~ None => e
    case e1 ~ Some("==" ~ e2) => Eq(e1,e2)
    case e1 ~ Some("!=" ~ e2) => NotEq(e1,e2)
    case e1 ~ Some("<" ~ e2) => Less(e1,e2)
    case e1 ~ Some(">" ~ e2) => Greater(e1,e2)
    case e1 ~ Some("<=" ~ e2) => AtMost(e1,e2)
    case e1 ~ Some(">=" ~ e2) => AtLeast(e1,e2)
  })
  
  def cmpOp = "==" | "!=" | "<" | "<=" | ">=" | ">" 
  
  def bitManipExpr: Parser[Expr] = positioned((addExpr ~ ((">>" | "<<" ) ~ addExpr *)) ^^{
    case e0 ~ rest => (rest foldLeft e0) {
      case (a, ">>" ~ b) => RShift(a,b)
      case (a, "<<" ~ b) => LShift(a,b)
    }
  }) 
  
  def addExpr: Parser[Expr] = positioned((mulExpr ~ (("+" | "-") ~ mulExpr *)) ^^{
    case e0 ~ rest => (rest foldLeft e0) {
            case (a, "+" ~ b) => Plus(a,b)
            case (a, "-" ~ b) => Minus(a,b) }
  })
  
  def mulExpr: Parser[Expr] = positioned((unaryExpr ~ (("*" | "/" | "%") ~ unaryExpr *)) ^^{
    case e0 ~ rest => (rest foldLeft e0) {
      case (a, "*" ~ b) => Times(a,b)
      case (a, "/" ~ b) => Div(a,b)
      case (a, "%" ~ b) => Mod(a,b) 
    }
  })
  
  
  
  def unaryExpr: Parser[Expr] = positioned(
    "-" ~> unaryExpr ^^ UnMinus | 
    "!" ~> unaryExpr ^^ Not |
    quantifier |
    "(" ~> expression <~ ")" ^^ { case e => e } |
    suffixExpr |
    functionApp |
    atom
  )
  
  def quantifier: Parser[Expr] = positioned(
    quantOp ~ repsep(declaration,",") ~ ("::" ~> (pattern ?) ~ expression) ^^ {
      case "forall" ~ decls ~ (pat ~ exp) => Forall(decls,exp,pat)
      case "exists" ~ decls ~ (pat ~ exp) => Exists(decls,exp,pat)
    }
  )
  
  def quantOp = "forall" | "exists"
  
  def declaration = positioned(typeName ~ ident ^^ {
    case (t ~ id) => Declaration(id,t,false)
  })
  
  def pattern: Parser[Expr] = positioned("{" ~> expression <~ "}")
  
  def portRef = positioned(ident ~ ("." ~> ident ?) ^^ {
    case a0 ~ None => PortRef(None,a0)
    case a0 ~ Some(a1) => PortRef(Some(a0),a1)
  })
  
  def functionApp: Parser[Expr] = positioned(
      (ident ~ ("(" ~> repsep(expression,",") <~ ")")) ^^ {
        case (id ~ params) => FunctionApp(id,params)
      })
  
  def suffixExpr: Parser[Expr] = positioned(
      (atom ~ ("[" ~> expression <~ "]")) ^^ {
        case (e ~ suffix) => IndexAccessor(e,suffix)
      })
  
  def atom: Parser[Expr] = positioned(
    boolLiteral | 
    identifier |
    indexSymbol |
    numericLit ^^ { case n => IntLiteral(n.toInt) }
  )
  
  def indexSymbol: Parser[Expr] = positioned(
    ("next" | "last") ^^ {f => IndexSymbol(f)}
  )
  
  def boolLiteral = positioned(
    "true" ^^^ BoolLiteral(true) |
    "false" ^^^ BoolLiteral(false)
  )
  
  def identifier = positioned(ident ^^ Id)
  
  def statementBody: Parser[List[Stmt]] = (statement *)
  
  def statement: Parser[Stmt] = positioned(
    "assert" ~> expression <~ Semi ^^ Assert |
    "assume" ~> expression <~ Semi ^^ Assume |
    identifier ~ ":=" ~ expression <~ Semi ^^ {
      case (id ~ _ ~ exp) => Assignment(id,exp)
    }
  )
  
  def typeName: Parser[Type] = positioned(
    "int" ^^^ IntType(32) |
    "bool" ^^^ BoolType
  )
}
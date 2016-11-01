package fi.abo.it.actortool

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator._
import scala.util.parsing.input.PagedSeqReader
import scala.collection.immutable.PagedSeq
import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional
import scala.util.parsing.input.NoPosition
import scala.util.matching.Regex
import java.io.File

import scala.language.postfixOps

class Parser extends StandardTokenParsers {
    
  def parseFile(file: File) = 
    phrase(programUnit)(new lexical.Scanner(new PagedSeqReader(PagedSeq fromFile file)))
  def Semi = ";" ?
    
  class LexerWithHex extends StdLexical {    
    lazy val hexDigits = "0123456789abcdefABCDEF".toArray.toSet
    def hexDigit = elem("hex digit",  hexDigits.contains(_))
    
    override def token: Parser[Token] =
      ('0' ~ 'x' ~ hexDigit ~ rep(hexDigit) ^^ { case '0' ~ 'x' ~ first ~ rest => HexaNumericLit(first :: rest mkString "") }
      | super.token
    )
    
    case class HexaNumericLit(chars: String) extends Token
  }
  
  override val lexical: LexerWithHex = new LexerWithHex()
  
  lexical.reserved += ("actor", "network", "unit", "action", "true", "false", "int", "bool", "uint", "size", 
                       "guard", "entities", "structure", "int", "bool", "invariant", "chinvariant", "end", 
                       "forall", "exists", "do", "assert", "assume", "initialize", "requires", "ensures", 
                       "var", "schedule", "fsm", "regexp", "List", "type", "function", "repeat", "priority",
                       "free", "primary", "error", "recovery", "next", "last", "prev", "public", "havoc"
                      )
  lexical.delimiters += ("(", ")", "<==>", "==>", "&&", "||", "==", "!=", "<", "<=", ">=", ">", "=",
                       "+", "-", "*", "/", "%", "!", ".", ";", ":", ":=", ",", "|", "[", "]",
                       "-->", "::", "{", "}", "<<" , ">>", "@", "&")
                       
  def programUnit = (actorDecl | networkDecl | unitDecl)*
  
  def annotation = positioned(("@" ~> ident) ^^ { case id => Annotation(id)})
  
  def unitDecl = positioned(("unit" ~> ident ~ (":" ~> (varDecl*)) <~ "end" ) ^^ {
    case (id ~ decls) => DataUnit(id,decls)
  })
  
  def actorDecl = positioned(
     ((annotation *) ~ 
         ("actor" ~> ident ~ 
         ("(" ~> repsep(formalParam,",") <~ ")" ?) ~ 
         repsep(inPortDecl,",") ~ 
         ("==>" ~> repsep(outPortDecl,",")) ~ 
         (":" ~> (actorMember*)) <~ "end")) ^^ {
       case (a ~ (id ~ Some(params) ~ inports ~ outports ~ members)) => 
         BasicActor(a, id, params, inports, outports, members)
       case (a ~ (id ~ None ~ inports ~ outports ~ members)) => 
         BasicActor(a, id, Nil, inports, outports, members)
    })
    
  def networkDecl = positioned(
      ((annotation *) ~
          ("network" ~> ident ~ 
          ("(" ~> repsep(formalParam,",") <~ ")" ?) ~ 
          repsep(inPortDecl,",") ~ 
          ("==>" ~> repsep(outPortDecl,",")) ~ 
          (":" ~> (networkMember*)) <~ "end")) ^^ {
      case (a ~ (id ~ Some(params) ~ inports ~ outports ~ members)) => 
        Network(a, id, params, inports, outports, members)
      case (a ~ (id ~ None ~ inports ~ outports ~ members)) => 
        Network(a, id, Nil, inports, outports, members)
    })
  
  def formalParam = positioned(
      (typeName ~ ident) ^^ {
        case (tName ~ id) => Declaration(id,tName,true,None)
      }  
    )
  def inPortDecl: Parser[InPort] = positioned((typeName ~ ident) ^^ {
    case (tName ~ id) => InPort(id,tName)
  })
  
  def outPortDecl: Parser[OutPort] = positioned((typeName ~ ident) ^^{
    case (tName ~ id) => OutPort(id,tName)
  })
  
  def actorMember: Parser[Member] = 
    positioned(actorInvDecl | chInvDecl | actionDecl | varDecl | scheduleBlock | priorityBlock | functionDecl)
  
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
  
  def functionDecl: Parser[FunctionDecl] =
    positioned(("function" ~> ident ~ ("(" ~> repsep(formalParam,",") <~ ")") ~ ("-->" ~> typeName) ~ (":" ~> expression) <~ "end") ^^ {
      case (name ~ inputs ~ output ~ body) => FunctionDecl(name,inputs,output,body)
    })
  //def schedType = "fsm" | "regexp" 
    
  def priorityBlock: Parser[Priority] = 
    positioned(("priority" ~> repsep(prioOrder,";") <~ "end") ^^ {
      case actions => Priority(actions)
    })
  
  def prioOrder = (ident ~ (">" ~> ident)) ^^ { case s1 ~ s2  => (Id(s1),Id(s2)) }
    
  def entityDecl = positioned(opt(annotation) ~ ident ~ ("=" ~> (ident ~ paramList)) ^^ {
    case None ~ name ~ (actorId ~ params) => Instance(name,actorId,params,Nil)
    case Some(annot) ~ name ~ (actorId ~ params) => Instance(name,actorId,params,List(annot))
  })
  
  def connection = positioned(opt(annotation) ~ opt(ident <~ ":") ~ (portRef ~ ("-->" ~> portRef)) ^^ {
    case None ~ id ~ (from ~ to) => Connection(id,from,to,Nil)
    case Some(annot) ~ id ~ (from ~ to) => Connection(id,from,to,List(annot))
  })
  
  def transition = positioned(ident ~ ("(" ~> ident <~ ")") ~ ("-->" ~> ident) ^^ {
    case (from ~ act ~ to)  => Transition(act,from,to)
  })
  
  def paramList: Parser[List[Expr]] = ("(" ~> repsep(expression,",") <~ ")" ^^ {
    case exps => exps
  })
  
  def actorInvDecl = positioned((opt("free") ~ opt("public") ~ "invariant" ~ expression) ^^ {
    case free ~ public ~ _ ~ expr => {
      ActorInvariant(Assertion(expr, free.isDefined),false, /*public.isDefined*/ true)
    }
  })
  
  def chInvDecl = positioned(( opt("free") ~ "chinvariant" ~ expression) ^^ {
    case None ~ _ ~ expr => ChannelInvariant(Assertion(expr,false),false)
    case Some(_) ~ _ ~ expr => ChannelInvariant(Assertion(expr,true),false)
  })
  
  def varDecl = positioned((typeName ~ ident ~ opt(("=" | ":=") ~ expression) <~ Semi) ^^ {
    case (typ ~ id ~ None) => Declaration(id,typ,false,None)
    case (typ ~ id ~ Some("=" ~ value)) => Declaration(id,typ,true,Some(value))
    case (typ ~ id ~ Some(":=" ~ value)) => Declaration(id,typ,false,Some(value))
  })
   
  def actionDecl: Parser[Action] = positioned(
    (((ident <~ ":")?) ~ 
        opt(actionClass) ~
        ("action" | "initialize") ~ 
        repsep(inputPattern,",") ~ 
        ("==>" ~> repsep(outputPattern,",")) ~
        ("guard" ~> expression ?) ~
        //("var" ~> repsep(varDecl,",") ?) ~
        ("requires" ~> expression *) ~
        ("ensures" ~> expression *) ~
        ("do" ~> statementBody ?)
        <~ "end") ^^ {
          case (id ~ cl ~ label ~ inputs ~ outputs ~ guard ~ /*vars ~*/ requires ~ ensures  ~ stmtOpt) => 
            val init = label == "initialize"
            val actClass = cl match {
              case Some("primary") => ActionClass.Primary
              case Some("error") => ActionClass.Error
              case Some("recovery") => ActionClass.Recovery
              case None => ActionClass.Normal
              case Some(x) => 
                // Should not happen
                throw new RuntimeException("Invalid keyword: " + x)
            }
            val stmt = stmtOpt match {
              case Some(s) => s
              case None => Nil
            }
            Action(id,actClass,init,inputs,outputs,guard,requires,ensures,/*vars.getOrElse(Nil)*/ Nil,stmt)
    }
  )
  
  def actionClass = ("primary" | "error" | "recovery")
  
  def inputPattern = inputPatternRng | inputPatternNum
  
  def inputPatternRng = positioned(
      (ident ~ (":" ~> "[" ~> repsep(identifier,",") <~ "]") ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ vars ~ Some(rep)) => InputPattern(port, vars, rep.toInt)
    case (port ~ vars ~ None) => InputPattern(port, vars, 1)
  })
  
  def inputPatternNum = positioned(
      (ident ~ (":" ~> numericLit) ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ num ~ Some(rep)) =>
      InputPattern(port, varList(port+"$v",num.toInt), rep.toInt)
    case (port ~ num ~ None) => 
      InputPattern(port, varList(port+"v",num.toInt), 1)
  })
  
  def outputPattern = outputPatternRng | outputPatternNum
  
  def outputPatternRng = positioned((ident ~ (":" ~> "[" ~> repsep(expression,",") <~ "]") ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ exps ~ Some(rep)) => OutputPattern(port, exps, rep.toInt)
    case (port ~ exps ~ None) => OutputPattern(port, exps, 1)
  })
  
  def outputPatternNum = positioned((ident ~ (":" ~> numericLit) ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ num ~ Some(rep)) => OutputPattern(port, varList(port+"$v",num.toInt), rep.toInt)
    case (port ~ num ~ None) => OutputPattern(port, varList(port+"$v",num.toInt), 1)
  })
  
  def varList(prefix: String, length: Int) = for (i <- List.range(0,length)) yield Id(prefix+"$"+i)

  
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
    case e1 ~ Some("=" ~ e2) => Eq(e1,e2)
    case e1 ~ Some("!=" ~ e2) => NotEq(e1,e2)
    case e1 ~ Some("<" ~ e2) => Less(e1,e2)
    case e1 ~ Some(">" ~ e2) => Greater(e1,e2)
    case e1 ~ Some("<=" ~ e2) => AtMost(e1,e2)
    case e1 ~ Some(">=" ~ e2) => AtLeast(e1,e2)
  })
  
  def cmpOp = "==" | "=" | "!=" | "<" | "<=" | ">=" | ">" 
  
  def bitManipExpr: Parser[Expr] = positioned((addExpr ~ ((">>" | "<<" | "&") ~ addExpr *)) ^^{
    case e0 ~ rest => (rest foldLeft e0) {
      case (a, ">>" ~ b) => RShift(a,b)
      case (a, "<<" ~ b) => LShift(a,b)
      case (a, "&" ~ b) => BWAnd(a,b)
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
    listLiteral |
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
    case (t ~ id) => Declaration(id,t,false,None)
  })
  
  def pattern: Parser[Expr] = positioned("{" ~> expression <~ "}")
  
  def portRef = positioned(ident ~ ("." ~> ident ?) ^^ {
    case a0 ~ None => PortRef(None,a0)
    case a0 ~ Some(a1) => PortRef(Some(a0),a1)
  })
  
  def functionApp = (functionAppSpecialMarker | functionAppStandard)
  
  def functionAppStandard: Parser[Expr] = positioned(
      (ident ~ opt(marker) ~ ("(" ~> repsep(expression,",") <~ ")")) ^^ {
        case (id ~ None ~ params) => FunctionApp(id,params)
        case (id ~ Some(sm) ~ params) => FunctionApp(id+sm.value,params)
      })
      
  def functionAppSpecialMarker: Parser[Expr] = positioned(
      (marker ~ ("(" ~> repsep(expression,",") <~ ")")) ^^ {
        case (SpecialMarker(m) ~ params) => FunctionApp(m,params)
      })
  
  def listLiteral: Parser[Expr] = positioned(
      ("[" ~> repsep(expression,",") <~ "]") ^^{
        case lst => ListLiteral(lst)
      })
      
  def suffixExpr: Parser[Expr] = positioned(
      (atom ~ ("[" ~> expression <~ "]")) ^^ {
        case (e ~ suffix) => IndexAccessor(e,suffix)
      })
  
  def atom: Parser[Expr] = positioned(
    boolLiteral | 
    identifier |
    marker |
    hexaNumericLit ^^ { case n => HexLiteral(n) } |
    numericLit ^^ { case n => IntLiteral(n.toInt) }
  )
  
  import lexical.HexaNumericLit
  
  def hexaNumericLit: Parser[String] =
    elem("hex-number", _.isInstanceOf[HexaNumericLit]) ^^ (_.chars)
  
  def boolLiteral = positioned(
    "true" ^^^ BoolLiteral(true) |
    "false" ^^^ BoolLiteral(false)
  )
  
  def marker = positioned( ("@" | "next" | "last" | "prev") ^^ { case n => SpecialMarker(n) } )
    
  def identifier = positioned(ident ^^ Id)
  
  def statementBody: Parser[List[Stmt]] = (statement *)
  
  def statement: Parser[Stmt] = positioned(
    "assert" ~> expression <~ Semi ^^ Assert |
    "assume" ~> expression <~ Semi ^^ Assume |
    "havoc" ~> repsep(ident,",") <~ Semi ^^ {case ids => Havoc(ids map { Id(_) })} |
    identifier ~ opt("[" ~> expression <~ "]") ~ (":=" ~> expression) <~ Semi ^^ {
      case (id ~ None ~ exp) => Assign(id,exp)
      case (id ~ Some(idx) ~ exp) => IndexAssign(id,idx,exp)
    }
  )
  
  
  def typeName = primType | compositeType 
  
  def primType: Parser[Type] = positioned(
    ("int" | "uint") ~ (opt("(" ~> "size" ~> "=" ~> numericLit <~ ")")) ^^ {
      case "int" ~ Some(size) => IntType(size.toInt)
      case "int" ~ None => IntType(32) 
      case "uint" ~ Some(size) => UintType(size.toInt) 
      case "uint" ~ None => UintType(32) 
    }
    | "bool" ^^^ BoolType
  )
  
  def compositeType: Parser[Type] = positioned(
    "List" ~> ("(" ~> "type" ~> ":" ~> typeName ~ ("," ~> "size" ~> "=" ~> numericLit) <~ ")") ^^ {
      case (contType ~ size) => ListType(contType,size.toInt)
    }
  )
}
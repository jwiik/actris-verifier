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
  
  var currFile: File = null
  
  def parseFile(file: File) = {
    currFile = file
    phrase(programUnit)(new lexical.Scanner(new PagedSeqReader(PagedSeq fromFile file)))
  }
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
                       "free", "primary", "error", "recovery", "next", "last", "prev", "stream", "havoc", "bv",
                       "Map", "if", "then", "else", "contract"
                      )
  lexical.delimiters += ("(", ")", "<==>", "==>", "&&", "||", "==", "!=", "<", "<=", ">=", ">", "=",
                       "+", "-", "*", "/", "%", "!", ".", ";", ":", ":=", ",", "|", "[", "]",
                       "-->", "::", "{", "}", "<<" , ">>", "@", "&", "~", "^", "->")
                       
  def programUnit = (actorDecl | networkDecl | unitDecl | typeDecl)*
  
  def annotation = filePositioned(("@" ~> ident) ^^ { case id => Annotation(id)})
  
  def unitDecl = filePositioned(("unit" ~> ident ~ (":" ~> (varDecl*)) <~ "end" ) ^^ {
    case (id ~ decls) => DataUnit(id,decls)
  })
  
  def actorDecl = filePositioned(
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
    
  def networkDecl = filePositioned(
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
  
  def typeDecl = filePositioned(("type" ~> ident ~ ("(" ~> repsep(formalParam,",") <~ ")" ?)) ^^ {
    case (id ~ Some(params)) => TypeDecl(RefType(id),params)
    case (id ~ None) => TypeDecl(RefType(id),Nil)
  })  
  
  def formalParam = filePositioned(
      (typeName ~ ident) ^^ {
        case (tName ~ id) => Declaration(id,tName,true,None)
      }  
    )
  def inPortDecl: Parser[InPort] = filePositioned((typeName ~ ident) ^^ {
    case (tName ~ id) => InPort(id,tName)
  })
  
  def outPortDecl: Parser[OutPort] = filePositioned((typeName ~ ident) ^^{
    case (tName ~ id) => OutPort(id,tName)
  })
  
  def actorMember: Parser[Member] = 
    filePositioned(actorInvDecl | chInvDecl | actionDecl | varDecl | scheduleBlock | priorityBlock | functionDecl | contractActionDecl)
  
  def networkMember: Parser[Member] = filePositioned(
      actorInvDecl | chInvDecl | entitiesBlock | structureBlock | actionDecl | contractActionDecl)
  
  def entitiesBlock: Parser[Entities] = filePositioned(("entities" ~> repsep(entityDecl,Semi) <~ (Semi?) <~ "end") ^^ {
    case entities => Entities(entities)
  })
  
  def structureBlock: Parser[Structure] = filePositioned(("structure" ~> repsep(connection,Semi) <~ (Semi?) <~ "end") ^^ {
    case connections => Structure(connections)
  })
  
  
  
  def scheduleBlock: Parser[Schedule] = 
    filePositioned(("schedule" ~> "fsm" ~ ident ~ (":" ~> repsep(transition,Semi) <~ (Semi?) <~ "end")) ^^ {
      case  "fsm" ~ init ~ transitions => Schedule(init,transitions)
    })
  
  def functionDecl: Parser[FunctionDecl] =
    filePositioned(("function" ~> ident ~ ("(" ~> repsep(formalParam,",") <~ ")") ~ ("-->" ~> typeName) ~ (":" ~> expression) <~ "end") ^^ {
      case (name ~ inputs ~ output ~ body) => FunctionDecl(name,inputs,output,body)
    })
  //def schedType = "fsm" | "regexp" 
    
  def priorityBlock: Parser[Priority] = 
    filePositioned(("priority" ~> repsep(prioOrder,";") <~ "end") ^^ {
      case actions => Priority(actions)
    })
  
  def prioOrder = (ident ~ (">" ~> ident)) ^^ { case s1 ~ s2  => (Id(s1),Id(s2)) }
    
  def entityDecl = filePositioned(opt(annotation) ~ ident ~ ("=" ~> (ident ~ paramList)) ^^ {
    case None ~ name ~ (actorId ~ params) => Instance(name,actorId,params,Nil)
    case Some(annot) ~ name ~ (actorId ~ params) => Instance(name,actorId,params,List(annot))
  })
  
  def connection = filePositioned(opt(annotation) ~ opt(ident <~ ":") ~ (portRef ~ ("-->" ~> portRef)) ^^ {
    case None ~ id ~ (from ~ to) => Connection(id,from,to,Nil)
    case Some(annot) ~ id ~ (from ~ to) => Connection(id,from,to,List(annot))
  })
  
  def transition = filePositioned(ident ~ ("(" ~> ident <~ ")") ~ ("-->" ~> ident) ^^ {
    case (from ~ act ~ to)  => Transition(act,from,to)
  })
  
  def paramList: Parser[List[Expr]] = ("(" ~> repsep(expression,",") <~ ")" ^^ {
    case exps => exps
  })
  
  def actorInvDecl = filePositioned((opt("free") ~ opt("stream") ~ "invariant" ~ expression) ^^ {
    case free ~ stream ~ _ ~ expr => {
      ActorInvariant(Assertion(expr, free.isDefined),false, stream.isDefined)
    }
  })
  
  def chInvDecl = filePositioned(( opt("free") ~ "chinvariant" ~ expression) ^^ {
    case None ~ _ ~ expr => ChannelInvariant(Assertion(expr,false),false)
    case Some(_) ~ _ ~ expr => ChannelInvariant(Assertion(expr,true),false)
  })
  
  def varDecl = filePositioned((typeName ~ ident ~ opt(("=" | ":=") ~ expression) <~ Semi) ^^ {
    case (typ ~ id ~ None) => Declaration(id,typ,false,None)
    case (typ ~ id ~ Some("=" ~ value)) => Declaration(id,typ,true,Some(value))
    case (typ ~ id ~ Some(":=" ~ value)) => Declaration(id,typ,false,Some(value))
  })
   
  def actionDecl: Parser[ActorAction] = filePositioned(
    (((ident <~ ":")?) ~ 
        ("action" | "initialize") ~ 
        repsep(inputPattern,",") ~ 
        ("==>" ~> repsep(outputPattern,",")) ~
        ("requires" ~> expression *) ~
        ("ensures" ~> expression *) ~
        ("guard" ~> expression ?) ~
        opt("var" ~> repsep(varDecl,",")) ~
        ("do" ~> statementBody ?)
        <~ "end") ^^ {
          case (id ~ label ~ inputs ~ outputs ~ requires ~ ensures ~ guard ~ vars  ~ stmtOpt) => 
            val init = label == "initialize"
            val stmt = stmtOpt match {
              case Some(s) => s
              case None => Nil
            }
            ActorAction(id,init,inputs,outputs,guard,requires,ensures,vars.getOrElse(Nil),stmt)
    }
  )
  
  def contractActionDecl: Parser[ContractAction] = filePositioned(
    (((ident <~ ":")?) ~ 
          "contract" ~
          repsep(inputPattern,",") ~ 
          ("==>" ~> repsep(outputPattern,",")) ~
          ("requires" ~> expression *) ~
          ("ensures" ~> expression *)
          <~ "end") ^^ {
            case (id ~ _ ~ inputs ~ outputs ~ requires ~ ensures) => 
              ContractAction(id, inputs map { ip => toNwPattern(ip) } , outputs map { op => toNwPattern(op) } ,requires,ensures)
    }
  )
   
  def toNwPattern(ip: InputPattern) = NwPattern(ip.portId, ip.vars.size)
  def toNwPattern(ip: OutputPattern) = NwPattern(ip.portId, ip.exps.size)
    
  def inputPattern = inputPatternRng | inputPatternNum
  
  def inputPatternRng = filePositioned(
      (ident ~ (":" ~> "[" ~> repsep(identifier,",") <~ "]") ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ vars ~ Some(rep)) => InputPattern(port, vars, rep.toInt)
    case (port ~ vars ~ None) => InputPattern(port, vars, 1)
  })
  
  def inputPatternNum = filePositioned(
      (ident ~ (":" ~> numericLit) ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ num ~ Some(rep)) =>
      InputPattern(port, varList(port+"$v",num.toInt), rep.toInt)
    case (port ~ num ~ None) => 
      InputPattern(port, varList(port+"v",num.toInt), 1)
  })
  
  def outputPattern = outputPatternRng | outputPatternNum
  
  def outputPatternRng = filePositioned((ident ~ (":" ~> "[" ~> repsep(expression,",") <~ "]") ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ exps ~ Some(rep)) => OutputPattern(port, exps, rep.toInt)
    case (port ~ exps ~ None) => OutputPattern(port, exps, 1)
  })
  
  def outputPatternNum = filePositioned((ident ~ (":" ~> numericLit) ~ opt("repeat" ~> numericLit)) ^^ {
    case (port ~ num ~ Some(rep)) => OutputPattern(port, varList(port+"$v",num.toInt), rep.toInt)
    case (port ~ num ~ None) => OutputPattern(port, varList(port+"$v",num.toInt), 1)
  })
  
  def varList(prefix: String, length: Int) = for (i <- List.range(0,length)) yield Id(prefix+"$"+i)

  
  def expression: Parser[Expr] = filePositioned(iffExpr) 
  
  def iffExpr: Parser[Expr] = filePositioned((implExpr ~ ("<==>" ~> iffExpr ?)) ^^ {
    case (e ~ None) => e
    case (e1 ~ Some(e2)) => Iff(e1,e2)
  })
  
  def implExpr: Parser[Expr] = filePositioned((logicalExpr ~ ("==>" ~> implExpr ?)) ^^ {
    case (e ~ None) => e
    case (e1 ~ Some(e2)) => Implies(e1,e2)
  })
  
  def logicalExpr: Parser[Expr] = filePositioned(cmpExpr ~ (( ("&&" ~ cmpExpr +) | ("||" ~ cmpExpr +) )?) ^^ {
    case e ~ None => e
    case e0 ~ Some(rest) => 
      (rest foldLeft e0) {
        case (a, "&&" ~ b) => And(a,b)
        case (a, "||" ~ b) => Or(a,b) 
      }
  })
  
  def cmpExpr: Parser[Expr] = filePositioned((bitManipExpr ~ ((cmpOp ~ bitManipExpr) ?)) ^^ {
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
  
  def bitManipExpr: Parser[Expr] = filePositioned((addExpr ~ ((">>" | "<<" | "&" | "|" | "^") ~ addExpr *)) ^^{
    case e0 ~ rest => (rest foldLeft e0) {
      case (a, ">>" ~ b) => RShift(a,b)
      case (a, "<<" ~ b) => LShift(a,b)
      case (a, "&" ~ b) => BwAnd(a,b)
      case (a, "|" ~ b) => BwOr(a,b)
      case (a, "^" ~ b) => BwXor(a,b)
    }
  }) 
  
  def addExpr: Parser[Expr] = filePositioned((mulExpr ~ (("+" | "-") ~ mulExpr *)) ^^{
    case e0 ~ rest => (rest foldLeft e0) {
            case (a, "+" ~ b) => Plus(a,b)
            case (a, "-" ~ b) => Minus(a,b) }
  })
  
  def mulExpr: Parser[Expr] = filePositioned((unaryExpr ~ (("*" | "/" | "%") ~ unaryExpr *)) ^^{
    case e0 ~ rest => (rest foldLeft e0) {
      case (a, "*" ~ b) => Times(a,b)
      case (a, "/" ~ b) => Div(a,b)
      case (a, "%" ~ b) => Mod(a,b) 
    }
  })
  
  
  
  def unaryExpr: Parser[Expr] = filePositioned(
    "-" ~> unaryExpr ^^ UnMinus | 
    "!" ~> unaryExpr ^^ Not |
    "~" ~> unaryExpr ^^ BwNot |
    quantifier |
    ifthenelse |
    "(" ~> expression <~ ")" ^^ { case e => e } |
    functionApp |
    suffixExpr |
    listLiteral |
    //range |
    atom
  )
  
  def quantifier: Parser[Expr] = filePositioned(
    quantOp ~ repsep(declaration,",") ~ ("::" ~> (pattern ?) ~ expression) ^^ {
      case "forall" ~ decls ~ (pat ~ exp) => Forall(decls,exp,pat)
      case "exists" ~ decls ~ (pat ~ exp) => Exists(decls,exp,pat)
    }
  )
  
  def ifthenelse: Parser[Expr] = filePositioned(
    (("if" ~> expression) ~ ("then" ~> expression) ~ ("else" ~> expression) <~ "end") ^^  {
      case cond ~ thn ~ els => IfThenElse(cond,thn,els)
    }
  )
      
  
  def quantOp = "forall" | "exists"
  
  def declaration = filePositioned(typeName ~ ident ^^ {
    case (t ~ id) => Declaration(id,t,false,None)
  })
  
  def pattern: Parser[Expr] = filePositioned("{" ~> expression <~ "}")
  
  def portRef = filePositioned(ident ~ ("." ~> ident ?) ^^ {
    case a0 ~ None => PortRef(None,a0)
    case a0 ~ Some(a1) => PortRef(Some(a0),a1)
  })
  
  def functionApp = (functionAppSpecialMarker | functionAppStandard)
  
  def functionAppStandard: Parser[Expr] = filePositioned(
      (ident ~ opt(marker) ~ ("(" ~> repsep(expression,",") <~ ")")) ^^ {
        case (id ~ None ~ params) => FunctionApp(id,params)
        case (id ~ Some(sm) ~ params) => FunctionApp(id+sm.value,params)
      })
      
  def functionAppSpecialMarker: Parser[Expr] = filePositioned(
      (marker ~ ("(" ~> repsep(expression,",") <~ ")")) ^^ {
        case (SpecialMarker(m) ~ params) => FunctionApp(m,params)
      })
  
  def listLiteral: Parser[Expr] = filePositioned(
      (("[" ~> repsep(expression,",") <~ "]") ^^{
        case lst => ListLiteral(lst)
      })
    ) 
//  def range: Parser[Expr] = filePositioned(
//      (numericLit ~ ".." ~ numericLit) ^^{
//        case start ~ ".." ~ end => Range(start.toInt,end.toInt)
//      })
  
  
  def suffixExpr: Parser[Expr] = filePositioned(
      atom ~ (suffixThing *) ^^ {
        case e ~ sfxs => sfxs.foldLeft(e) { (t,a) => val result = a(t); result.setPos(t.pos) }
      }
  )
  
  def suffixThing: Parser[(Expr => Expr)] = {
    (("[" ~> expression <~ "]") ^^ {case e1 => { e0: Expr => IndexAccessor(e0,e1)}}
    | ("." ~> ident) ^^ {case e1 => { e0: Expr => FieldAccessor(e0,e1)}})
  }
  
  def atom: Parser[Expr] = filePositioned(
    boolLiteral | 
    identifier |
    marker |
    hexaNumericLit ^^ { case n => HexLiteral(n) } |
    numericLit ^^ { case n => IntLiteral(n.toInt) }
  )
  
  import lexical.HexaNumericLit
  
  def hexaNumericLit: Parser[String] =
    elem("hex-number", _.isInstanceOf[HexaNumericLit]) ^^ (_.chars)
  
  def boolLiteral = filePositioned(
    "true" ^^^ BoolLiteral(true) |
    "false" ^^^ BoolLiteral(false)
  )
  
  def marker = filePositioned( ("@" | "next" | "last" | "prev") ^^ { case n => SpecialMarker(n) } )
    
  def identifier = filePositioned(ident ^^ Id)
  
  def statementBody: Parser[List[Stmt]] = (statement *)
  
  def statement: Parser[Stmt] = filePositioned(
    "assert" ~> expression <~ Semi ^^ Assert |
    "assume" ~> expression <~ Semi ^^ Assume |
    "havoc" ~> repsep(ident,",") <~ Semi ^^ {case ids => Havoc(ids map { Id(_) })} |
    (identifier ~ (":=" ~> expression) <~ Semi ^^ {
      case (id ~ exp) => Assign(id,exp)
    }) |
    (suffixExpr ~ (":=" ~> expression) <~ Semi ^^ {
      case (id ~ exp) => MapAssign(id,exp)
    })
  )
  
  //def assignable = suffixExpr | identifier
  
  
  def typeName = primType | compositeType 
  
  def primType: Parser[Type] = filePositioned(
    (("int" | "uint") ~ (opt("(" ~> "size" ~> "=" ~> numericLit <~ ")")) ^^ {
      case "int" ~ Some(size) => IntType(size.toInt)
      case "int" ~ None => IntType(-1) 
      case "uint" ~ Some(size) => UintType(size.toInt) 
      case "uint" ~ None => UintType(-1) 
    })
    | (("bv" ~> "(" ~> "size" ~> "=" ~> numericLit <~ ")") ^^ {
      case size => BvType(size.toInt)
    })
    | "bool" ^^^ BoolType
  )
  
  def compositeType: Parser[Type] = filePositioned(
    ("List" ~> ("(" ~> "type" ~> ":" ~> typeName ~ ("," ~> "size" ~> "=" ~> numericLit) <~ ")") ^^ {
      case (contType ~ size) => ListType(contType,size.toInt)
    }) |
    ("Map" ~> ("(" ~>  typeName ~ "->" ~ typeName) <~ ")" ^^ {
      case (domainType ~ "->" ~ rangeType) => MapType(domainType,rangeType)
    }) |
    (ident ^^ {case id => RefType(id)})
  )
  
  def filePositioned[T <: ASTNode](p : => Parser[T]) : Parser[T] = Parser {
    in => p(in) match {
      case Success(t, in1) => {
        if (t.pos == NoFilePosition) t.setPos(Some(currFile.getName),in.pos)
        Success(t,in1)
      }
      case ns: NoSuccess => ns
    }
  }
}
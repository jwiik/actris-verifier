package fi.abo.it.actortool

import collection.mutable.ListBuffer
import fi.abo.it.actortool.util.ASTPrinter

trait Preprocessor {
  def process(program: List[TopDecl]): List[TopDecl]
  def |(processor: Preprocessor) = new ComposedProcessor(this,processor)
}

case class ComposedProcessor(processor1: Preprocessor, processor2: Preprocessor) extends Preprocessor {
  def process(program: List[TopDecl]): List[TopDecl] = processor2.process(processor1.process(program))
}

case object InitActionNormaliser extends Preprocessor {
  
  def process(program: List[TopDecl]): List[TopDecl] = {
    for (unit <- program) yield {
      unit match {
        case ba: BasicActor => {
          val oldMembers = ba.members
          val inits = ba.variables.filter { d => d.value.isDefined && !d.constant }

          val initAction = 
            ba.actorActions.find { a => a.init } match {
              case Some(initAction) => {
                addVarInitialisations(initAction, inits)
              }
              case None => {
                var initAction = ActorAction(Some(ba.id + "#gen$init"),true,Nil,Nil,Nil,Nil,Nil,Nil,Nil)
                addVarInitialisations(initAction, inits)
              }
            }
          val newMembers = 
            initAction ::
            ba.members.filterNot { 
              m => {
                m match { 
                  case ActorAction(_,true,_,_,_,_,_,_,_) => true
                  case _ => false
                }
              }
            }
          
          BasicActor(ba.id,ba.parameters,ba.inports,ba.outports,newMembers).withAnnotationsFrom(ba)
          
        }
        case _ => unit
      }
    }
  }
  
  def addVarInitialisations(ia: ActorAction, inits: List[Declaration]): ActorAction = {
    val initAssigns = inits map { d => Assign(Id(d.id).setPos(d.pos),d.value.get).setPos(d.pos) }
    val newStmt = initAssigns ::: ia.body
    ActorAction(ia.label,ia.init,ia.inputPattern,ia.outputPattern,ia.guards,ia.requires,ia.ensures,ia.variables,newStmt).setPos(ia.pos)
  }
}

/**
 * This preprocessor maps the action schedule into a state variable and action guards.
 * It requires that the actor has an initialize actor.
 */
case object ActionScheduleProcessor extends Preprocessor {
  
  def process(program: List[TopDecl]): List[TopDecl] = {
    for (unit <- program) yield {
      unit match {
        case ba: BasicActor => {
          ba.schedule match {
            case Some(schedule) => mapScheduleToGuards(ba, schedule)
            case None => unit
          }
        }
        case _ => unit
      }
    }
  }
  
  def mapScheduleToGuards(a: BasicActor, s: Schedule): BasicActor = {
    var hasInitAction = false
    val members = a.members.filterNot { m => m.isSchedule }
    var newMembers = {
      for (m <- members) yield {
        m match {
          case ActorAction(labelOpt,init,inputPattern,outputPattern,guard,requires,ensures,variables,body) => {
            var newBody = body
            var newGuards = guard
            var newEnsures = ensures
            
            if (!init && labelOpt.isDefined) {
              val transitionData: List[(Expr,(Expr,List[Stmt]),(Expr,Expr))] = {
                for (t <- s.transitions.filter { t => t.action == labelOpt.get }) yield {
                   val guard = Eq(Id("St#"),Id(t.from))
                   val stUpdate = (guard, List(Assign(Id("St#"),Id(t.to))))
                   val stFromTo = (Eq(FunctionApp("old",List(Id("St#"))),Id(t.from)), Eq(Id("St#"),Id(t.to)))
                   (guard,stUpdate,stFromTo)
                }
              }
              val (guards,stUpdates, stFromTo) = transitionData.unzip3
              
              if (!guards.isEmpty) {
                newGuards = newGuards :+ guards.reduceLeft { (a,b) => Or(a,b) }
              }
              if (!stUpdates.isEmpty) {
                val (g,s) = stUpdates.head
                if (stUpdates.length == 1) {
                  newBody = newBody ++ s
                }
                else {
                  newBody = newBody ++ List(IfElse(g,s, stUpdates.tail map { case (g1,s1) => ElseIf(g1,s1) } ,Nil))
                }
              }
              
              if (stFromTo.isEmpty) {}
              else if (stFromTo.size == 1) {
                val (_,to) = stFromTo.head
                newEnsures = newEnsures :+ Assertion(to,true) 
              }
              else {
                newEnsures = newEnsures :+ Assertion(stFromTo.map{ case (from,to) => Implies(from,to): Expr }.reduceLeft((a,b) => And(a,b)),true)
              }
              
            }
            else if (init) {
              hasInitAction = true
              newBody = body ::: List(Assign(Id("St#"),Id(s.initState)))
              newEnsures = newEnsures :+ Assertion(Eq(Id("St#"),Id(s.initState)),true) 
            }
            
            val action = ActorAction(labelOpt,init,inputPattern,outputPattern,newGuards,requires,newEnsures,variables,newBody)
            action.setPos(m.pos)
          }
          case _ => m
        }
      }
    }
    
    if (!hasInitAction) throw new IllegalArgumentException("ActionSchedule preprocessor requires that each actor has an init action")
    
    
    for ((state,i) <- s.states.zipWithIndex) {
      val lit = IntLiteral(i); lit.typ = StateType(a,s.states)
      newMembers = Declaration(state,StateType(a,s.states),true,Some(lit)) :: newMembers
    }
    newMembers = Declaration("St#",StateType(a,s.states),false,None) :: newMembers
    val statePreds: List[Expr] = s.states map {st => Eq(Id("St#"),Id(st)).setPos(s.pos) }
    val predicate = statePreds.reduceLeft((a,b) => Or(a,b)).setPos(s.pos)
    newMembers = ActorInvariant(Assertion(predicate,false,None),true,false) :: newMembers
    val actor = 
      BasicActor(
        a.id,
        a.parameters,
        a.inports,
        a.outports,
        newMembers).withAnnotationsFrom(a)
    actor.setPos(a.pos)
  }
  
}


case object ProcedureExpander extends Preprocessor {
  
  def process(program: List[TopDecl]): List[TopDecl] = {
    for (unit <- program) yield {
      unit match {
        case ba: BasicActor => expandProcedureCalls(ba)
        case _ => unit
      }
    }
  }
  
  def expandProcedureCalls(ba: BasicActor): BasicActor = {
    val procedureDecls = ba.procedureDecls.map(pd => (pd.name,pd)).toMap
    
    
    val newMembers = for (m <- ba.members) yield {
      m match {
        case a: ActorAction => 
          val newDecls = collection.mutable.Set[Declaration]()
          val newBody = expandProcedureCalls(procedureDecls,newDecls,a.body)
          List(ActorAction(a.label, a.init, a.inputPattern, a.outputPattern, a.guards, a.requires, a.ensures, a.variables ++ newDecls , newBody))
        case pd: ProcedureDecl => Nil 
        case x => List(x)
      }
    }
    
    val a = BasicActor(ba.id,ba.parameters,ba.inports,ba.outports,newMembers.flatten).withAnnotationsFrom(ba)
    a
  }
  
  def expandProcedureCalls(decls: Map[String,ProcedureDecl], newDecls:  collection.mutable.Set[Declaration], stmt: List[Stmt]): List[Stmt] = {
    val newStmt = new ListBuffer[Stmt]
    for (s <- stmt) {
      s match {
        case ProcCall(name,inputs) => {
          decls.get(name) match {
            case Some(pd) => {
              val inputReplacements = pd.inputs.zip(inputs).map { case (p,a) => Id(p.id) -> a }
              val newVars = pd.variables.map { v => Declaration(pd.name+"#"+v.id,v.typ,v.constant,v.value)  }
              newDecls ++= newVars
              val varReplacements = pd.variables.map { v => Id(v.id) -> Id(pd.name+"#"+v.id)  }
              val replacements = (inputReplacements ::: varReplacements).toMap
              val replacedProcedureBody = IdReplacer.visitStmt(pd.body)(replacements)
              newStmt ++= replacedProcedureBody
            }
            case None => throw new RuntimeException()
          }
        }
        case IfElse(cond,thn,elsifs,els) =>
          newStmt += IfElse(
              cond,
              expandProcedureCalls(decls,newDecls,thn),
              elsifs.map { e => ElseIf(e.cond, expandProcedureCalls(decls,newDecls,e.stmt)) } ,
              expandProcedureCalls(decls,newDecls,els))
        case While(cond,inv,body) => newStmt += While(cond,inv,expandProcedureCalls(decls,newDecls,body))
        case x => newStmt += x
      }
    }
    newStmt.toList
  }
  
}

/**
 * This preprocessor unrolls foreach loops. In contrast to most other preprocessors this preprocessor must
 * be called after typechecking.
 */
case object ForEachExpander extends Preprocessor {
  def process(program: List[TopDecl]): List[TopDecl] = {
    for (unit <- program) yield {
      unit match {
        case ba: BasicActor => unrollLoops(ba)
        case _ => unit
      }
    }
  }
  
  def unrollLoops(ba: BasicActor): BasicActor = {
    val newMembers = for (m <- ba.members) yield {
      m match {
        case a: ActorAction => 
          val newDecls = collection.mutable.Set[Declaration]()
          val newBody = unrollLoops(newDecls, a.body)
          ActorAction(a.label, a.init, a.inputPattern, a.outputPattern, a.guards, a.requires, a.ensures, a.variables ++ newDecls , newBody)
        case x => x
      }
    }
    
    val a = BasicActor(ba.id,ba.parameters,ba.inports,ba.outports,newMembers).withAnnotationsFrom(ba)
    a
  }
  
  def unrollLoops(newDecls: collection.mutable.Set[Declaration], stmt: List[Stmt]): List[Stmt] = {
    val newStmt = new ListBuffer[Stmt]
    for (s <- stmt) {
      s match {
        case ForEach(v,iterand,invs,body) => {
          newDecls += Declaration(v.id,v.typ,false,None)
          val vId = Id(v.id); vId.typ = v.typ
          val size = iterand.typ.asInstanceOf[MapType].size
          for (i <- 0 until size) {
            val accessor = iterand match {
              // If the iterand is a list literal, we can directly pick the correct element (reducing the AST)
              case ListLiteral(lst) => lst(i)
              case _ => IndexAccessor(iterand,IntLiteral(i).withType(IntType)).withType(v.typ)
            }
            newStmt += Assign(vId,accessor)
            newStmt ++= body
          }
        }
        case IfElse(cond,thn,elsifs,els) =>
          newStmt += IfElse(
              cond,
              unrollLoops(newDecls,thn),
              elsifs.map { e => ElseIf(e.cond, unrollLoops(newDecls,e.stmt)) } ,
              unrollLoops(newDecls,els))
        case While(cond,inv,body) => newStmt += While(cond,inv,unrollLoops(newDecls,body))
        case x => newStmt += x
      }
    }
    newStmt.toList
  }
}

/**
 * This preprocessor unrolls foreach loops. In contrast to most other preprocessors this preprocessor must
 * be called after typechecking.
 */
case object RangeExpander extends BasicActorExprAndStmtReplacer {
  
  def replace(stmt: List[Stmt]): List[Stmt] = RangeReplacer.visitStmt(stmt)(Map.empty)
  def replace(expr: Expr): Expr = RangeReplacer.visitExpr(expr)(Map.empty)
  
  object RangeReplacer extends ASTReplacingVisitor[Unit] {
    override def visitExpr(expr: Expr)(implicit map: Unit): Expr = {
      expr match {
        case rng@Range(str,end) => {
          val size = rng.typ.asInstanceOf[MapType].size
          var list = List[Expr](str)
          for (i <- 1 until size) {
            list = list :+ (str match {
              // This is to avoid unnecessary additions with zero
              case IntLiteral(0) => IntLiteral(i).withType(IntType)
              case _ => Plus(str,IntLiteral(i).withType(IntType)).withType(IntType)
            })
          }
          ListLiteral(list).withType(rng.typ)
        }
        case cmpr@Comprehension(expr,v,iter) => {
          val nExpr = visitExpr(expr)
          val nIter = visitExpr(iter)
          val lstType = nIter.typ.asInstanceOf[MapType]
          var list = List[Expr]()
          nIter match {
            case ListLiteral(lst) => {
              for (l <- lst) {
                assert(l.typ != null)
                val el = IdReplacerString.visitExpr(nExpr)(Map(v.id -> l))
                assert(el.typ != null)
                list = list :+ el
              }
            }
            case x => {
              for (i <- 0 until lstType.size) {
                val acc = IndexAccessor(x,IntLiteral(i).withType(IntType)).withType(lstType.rangeType)
                list = list :+ IdReplacerString.visitExpr(nExpr)(Map(v.id -> acc))
              }
            }
          }
          
          MapLiteral(v.typ,list).withType(cmpr.typ)
        }
        case _ => super.visitExpr(expr)
      }
    }
  }
  
}

case object EnumLiteralToBvHandler extends BasicActorExprAndStmtReplacer {
  
  def replace(stmt: List[Stmt]): List[Stmt] = EnumLiteralHandler.visitStmt(stmt)(Map.empty)
  def replace(expr: Expr): Expr = EnumLiteralHandler.visitExpr(expr)(Map.empty)
  
  object EnumLiteralHandler extends ASTReplacingVisitor[Unit] {
    override def visitExpr(expr: Expr)(implicit map: Unit): Expr = {
      expr match {
        case FunctionApp("int",List(ListLiteral(lst),s)) => {
          ListLiteral(
            lst.map { l =>
              l match {
                case il: IntLiteral => FunctionApp("int",List(il,s))
                case _ => throw new RuntimeException()
              }
            }
          )
        }
        case FunctionApp("int",List(MapLiteral(dom,lst),s)) => {
          MapLiteral(dom,
            lst.map { l =>
              l match {
                case il: IntLiteral => FunctionApp("int",List(il,s))
                case _ => throw new RuntimeException()
              }
            }
          )
        }
        case _ => super.visitExpr(expr)
      }
    }
  }
  
}

abstract class BasicActorExprAndStmtReplacer extends Preprocessor {
  
  def process(program: List[TopDecl]): List[TopDecl] = {
    for (unit <- program) yield {
      unit match {
        case ba: BasicActor => replace(ba)
        case _ => unit
      }
    }
  }
  
  def replace(ba: BasicActor): BasicActor = {
    val newMembers = for (m <- ba.members) yield {
      m match {
        case a: ActorAction => 
          val newBody = replace(a.body)
          val newOpats = a.outputPattern.map { 
            o => OutputPattern(o.portId, o.exps.map(replace), o.repeat).withType(o.typ) 
          }
          val newVars = a.variables.map {
            d => 
              val value = d.value match {
                case Some(v) => Some(replace(v))
                case None => None
              }
              Declaration(d.id,d.typ,d.constant,value) 
          }
          ActorAction(a.label, a.init, a.inputPattern, newOpats, a.guards, a.requires, a.ensures, newVars , newBody)
        case d: Declaration => {
          val value = d.value match {
            case Some(v) => Some(replace(v))
            case None => None
          }
          Declaration(d.id,d.typ,d.constant,value) 
        }
        case x => x
      }
    }
    
    val a = BasicActor(ba.id,ba.parameters,ba.inports,ba.outports,newMembers).withAnnotationsFrom(ba)
    a
  }
  
  def replace(expr: Expr): Expr
  def replace(stmt: List[Stmt]): List[Stmt]

}




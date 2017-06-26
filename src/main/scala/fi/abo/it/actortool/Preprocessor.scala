package fi.abo.it.actortool

import collection.mutable.ListBuffer

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
          
          BasicActor(ba.annotations,ba.id,ba.parameters,ba.inports,ba.outports,newMembers)
          
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
            
            if (!init && labelOpt.isDefined) {
              val transitionData: List[(Expr,(Expr,List[Stmt]))] = {
                for (t <- s.transitions.filter { t => t.action == labelOpt.get }) yield {
                   val guard = Eq(Id("St#"),Id(t.from))
                   val stUpdate = (guard, List(Assign(Id("St#"),Id(t.to))))
                   (guard,stUpdate)
                }
              }
              val (guards,stUpdates) = transitionData.unzip
              
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
            }
            else if (init) {
              hasInitAction = true
              newBody = body ::: List(Assign(Id("St#"),Id(s.initState)))
            }
            
            val action = ActorAction(labelOpt,init,inputPattern,outputPattern,newGuards,requires,ensures,variables,newBody)
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
        a.annotations,
        a.id,
        a.parameters,
        a.inports,
        a.outports,
        newMembers)
    actor.setPos(a.pos)
  }
  
}


object NetworkFlattener extends Preprocessor {
  
  override def process(program: List[TopDecl]): List[TopDecl] = {
    
    val actorDeclarations = 
      (program flatMap { unit =>
        unit match {
          case nw: Network => List((nw.id,nw))
          case ba: BasicActor => List((ba.id,ba))
          case _ => Nil
        }
      }).toMap
    
    for (unit <- program) yield {
      unit match {
        case nw@Network(annots,id,params,inports,outports,members) => {
          val (entities,cons) = flattenRec(nw, actorDeclarations)
          val filterMembers = members.filterNot { x => x.isStructure || x.isEntities }
          val newMembers = Entities(entities)::Structure(cons)::filterMembers
          Network(annots,id,params,inports,outports,newMembers)
        }
        case _ => unit
      }
    }
  }
  
  def flattenRec(nw: Network, actors: Map[String,DFActor]): (List[Instance],List[Connection]) = {
    val entities = new ListBuffer[Instance]
    val connections = new ListBuffer[Connection]
    val channelMapping = Util.buildConnectionMap(nw.structure.get.connections)

    val ownEntities = nw.entities.get.entities
    //val ownConnections = nw.structure.get.connections.filterNot { c =>  c.isInput || c.isOutput }
    //val ownIoConnections = nw.structure.get.connections.filter { c =>  c.isInput || c.isOutput }
    
    
    val nonNwConns = nw.structure.get.connections.filter { 
        c => {
          (c.from match {
            case PortRef(Some(id),_) => !actors(ownEntities.find(x => x.id == id).get.actorId ).isInstanceOf[Network]
            case PortRef(None,_) => true
          }) &&
          (c.to match {
            case PortRef(Some(id),_) => !actors(ownEntities.find(x => x.id == id).get.actorId ).isInstanceOf[Network]
            case PortRef(None,_) => true
          })
        }
      }
    
    connections ++= nonNwConns
    
    for (e <- ownEntities) {
      val actor = actors(e.actorId)
      actor match {
        case subnw: Network => {
          val (subEntities,subConnections) = flattenRec(subnw,actors)
          for (se <- subEntities) {
            entities += Instance(e.id+"#"+se.id,se.actorId,se.arguments,se.annotations)
          }
          //entities ++= subEntities
          for (sc <- subConnections) {
            val from = if (sc.from.actor.isDefined) Some(e.id+"#"+sc.from.actor.get) else None
            val to = if (sc.to.actor.isDefined) Some(e.id+"#"+sc.to.actor.get) else None
            connections += Connection(sc.label,PortRef(from,sc.from.name),PortRef(to,sc.to.name),sc.annotations)
          }
          //connections ++= subConnections
          
          val subChanMapping = Util.buildConnectionMap(subConnections)
          for (p <- actor.inports) {
            val subActorPortRef = subChanMapping(PortRef(None,p.id)).to
            val parentActorPortRef = channelMapping(PortRef(Some(e.id),p.id)).from
            val con = Connection(Some(e.id+"#"+p.id+"$chan"),parentActorPortRef,subActorPortRef,Nil)
            connections += con
          }
          for (p <- actor.outports) {
            val subActorPortRef = subChanMapping(PortRef(None,p.id)).from
            val parentActorPortRef = channelMapping(PortRef(Some(e.id),p.id)).to
            val con = Connection(Some(e.id+"#"+p.id+"$chan"),parentActorPortRef,subActorPortRef,Nil)
            connections += con
          }
          
        }
        case ba: BasicActor => entities += e
      }
    }
    
    (entities.toList,connections.toList)
  }
  
}


class RepeatUnroller extends Preprocessor {
  // STUB, not in working state  
  def process(program: List[TopDecl]): List[TopDecl] = {
    for (unit <- program) yield {
      unit match {
        case ba: BasicActor => unrollRepeats(ba)
        case _ => unit
      }
    }
  }
  
  def unrollRepeats(ba: BasicActor): BasicActor = {
    val newMembers = {
      for (m <- ba.members) yield {
        m match {
          case a: ActorAction => {
            for (ip <- a.inputPattern) yield {
              
            }
          }
          case x => x
        }
      }
    }
    ba
  }
  
}

/**
 * This preprocessor transforms function calls in actor bodies
 * to be called in a separate statement. This also includes output
 * patterns.
 */
//object FunctionCallNormaliser extends Preprocessor {
//  def process(program: List[TopDecl]): List[TopDecl] = {
//    for (unit <- program) yield {
//      unit match {
//        case BasicActor(annots,id,params,inports,outports,members) => 
//          val newMembers = {
//            for (m <- members) yield {
//              m match {
//                case a: ActorAction => transformFunCallsInAction(a)
//                case _ => m
//              }
//            }
//          }
//          BasicActor(annots,id,params,inports,outports,newMembers)
//        case _ => unit
//      }
//    }
//  }
//  
//  def transformFunCallsInAction(a: ActorAction): ActorAction = {
//    val newTempVarDeclarations = new ListBuffer[Declaration]
//    val newBody = transformStatement(a.body, newTempVarDeclarations)
//    ActorAction(a.label,a.init,a.inputPattern,a.outputPattern,a.guards,a.requires,a.ensures,a.variables,newBody)
//  }
//  
//  val funCallCollector = new FunCallCollector
//  val funCallReplacer = new FunCallReplacer
//  
//  def transformStatement(stmt: List[Stmt], newTempVarDecls: ListBuffer[Declaration]) = {
//    val newStmt = new ListBuffer[Stmt]
//    
//    for (s <- stmt) {
//      s match {
//        case Assign(v,exp) => {
//          println("==")
//          val replMap = collection.mutable.Map[FunctionApp,Id]()
//          val calls = funCallCollector.collectFunCalls(exp)
//          println("Calls: " + calls)
//          var e = exp
//          for (c <- calls) {
//            println(e)
//            val replId = Id("test")
//            replMap(c) = replId
//            //newTempVarDecls += Declaration(replId.id,c.ty)
//            e = funCallReplacer.visitExpr(e)(replMap.toMap)
//            newStmt += Assign(replId,c)
//          }
//          newStmt += Assign(v,e)
//        }
//      }
//    }
//    newStmt.toList
//  }
//  
//  class FunCallReplacer extends ASTReplacingVisitor[FunctionApp,Id] {
//    override def visitExpr(expr: Expr)(implicit map: Map[FunctionApp,Id]): Expr = {
//      expr match {
//        case fa: FunctionApp => {
//          if (map contains fa) map(fa)
//          else {
//            val args = visitExpr(fa.parameters)
//            FunctionApp(fa.name,args)
//          }
//        }
//        case _ => super.visitExpr(expr)
//      }
//    }
//  }
//  
//  class FunCallCollector extends ASTVisitor[ListBuffer[FunctionApp]] {
//    
//    def collectFunCalls(expr: Expr): List[FunctionApp] = {
//      val calls = new ListBuffer[FunctionApp]
//      visitExpr(expr)(calls)
//      calls.toList
//    }
//    
//    override def visitExpr(expr: Expr)(implicit info: ListBuffer[FunctionApp]) {
//       expr match {
//         case fa@FunctionApp(name,args) => {
//           for (a <- args) visitExpr(a)
//           info += fa
//         }
//         case x => super.visitExpr(x)
//       }
//     }
//  }
//  
//}



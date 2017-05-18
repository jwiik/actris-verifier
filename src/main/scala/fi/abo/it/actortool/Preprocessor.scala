package fi.abo.it.actortool

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
          if (inits.isEmpty) {
            ba
          }
          else {
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
    var newMembers =
      for (m <- members) yield {
        m match {
          case ActorAction(labelOpt,init,inputPattern,outputPattern,guard,requires,ensures,variables,body) => {
            var newBody = body
            var newGuards = guard
            
            if (!init && labelOpt.isDefined) {
              val transitionData: List[(Expr,(Expr,List[Stmt]))] =
                for (t <- s.transitions.filter { t => t.action == labelOpt.get }) yield {
                   val guard = Eq(Id("St#"),Id(t.from))
                   val stUpdate = (guard, List(Assign(Id("St#"),Id(t.to))))
                   (guard,stUpdate)
                }
              
              val (guards,stUpdates) = transitionData.unzip
              
              if (!guards.isEmpty) {
                newGuards = newGuards :+ guards.reduceLeft { (a,b) => Or(a,b) }
              }
              if (!stUpdates.isEmpty) {
                val (g,s) = stUpdates.head
                newBody = newBody ++ List(IfElse(g,s, stUpdates.tail map { case (g1,s1) => ElseIf(g1,s1) } ,Nil))
              }
            }
            else if (init) {
              newBody = body ::: List(Assign(Id("St#"),Id(s.initState)))
            }
            
            val action = ActorAction(labelOpt,init,inputPattern,outputPattern,newGuards,requires,ensures,variables,newBody)
            action.setPos(m.pos)
          }
          case _ => m
        }
      }
    for ((state,i) <- s.states.zipWithIndex) {
      newMembers = Declaration(state,StateType(a,s.states),true,Some(IntLiteral(i))) :: newMembers
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
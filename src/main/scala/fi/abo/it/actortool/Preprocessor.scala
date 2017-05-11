package fi.abo.it.actortool

trait Preprocessor {
  def process(program: List[TopDecl]): List[TopDecl]
}

class ActionScheduleProcessor extends Preprocessor {
  
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
    
    val members = a.members.filterNot { m => m.isSchedule }
    var newMembers =
      for (m <- members) yield {
        m match {
          case ActorAction(Some(label),init,inputPattern,outputPattern,guard,requires,ensures,variables,body) => {
            var newBody = body
            var newGuards = guard
            
            val transitionData: List[(Expr,(Expr,List[Stmt]))] =
              for (t <- s.transitions.filter { t => t.action == label }) yield {
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
            
            if (init) {
              newBody = body ::: List(Assign(Id("St#"),Id(s.initState)))
            }
            val action = ActorAction(Some(label),init,inputPattern,outputPattern,newGuards,requires,ensures,variables,newBody)
            action.setPos(m.pos)
          }
          case _ => m
        }
      }
    for ((state,i) <- s.states.zipWithIndex) {
      newMembers = Declaration(state,IntType,true,Some(IntLiteral(i))) :: newMembers
    }
    newMembers = Declaration("St#",IntType,false,None) :: newMembers  
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
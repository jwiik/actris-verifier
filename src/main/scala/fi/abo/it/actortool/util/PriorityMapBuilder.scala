package fi.abo.it.actortool.util

import fi.abo.it.actortool._

object PriorityMapBuilder {
  
  def buildPriorityMap(actor: DFActor, subComponent: Boolean, alwaysUseContracts: Boolean): Map[AbstractAction,List[AbstractAction]] = {
    if (subComponent && !actor.contractActions.isEmpty && (actor.isNetwork || alwaysUseContracts || actor.hasAnnotation("merge")) ) {
      return (actor.contractActions map { a => (a,Nil: List[AbstractAction]) }).toMap
    }
    
    var orderedActions: Map[AbstractAction,List[AbstractAction]] = 
      (actor.actorActions filter { a => !a.init } map {a => (a,Nil: List[AbstractAction])}).toMap
    
    actor.priority match {
      case Some(pr) => {
        for ((a1,a2) <- pr.orders) {
          // Assuming valid label
          val act1 = actor.actorActions.find{ a => a.fullName == a1.id }.get
          val act2 = actor.actorActions.find{ a => a.fullName == a2.id }.get
          // act1 is the higher prio action. We now add act1 as a higher prio action to act2
          val current = act1 :: orderedActions(act2)
          orderedActions = orderedActions + (act2 -> current)
        }
      }
      case None =>
    }
    orderedActions
  }
  
}
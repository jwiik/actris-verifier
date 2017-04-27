package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer

class BasicActorTranslator(
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    val typeCtx: Resolver.Context) extends EntityTranslator[BasicActor] {

  val actorVerStructBuilder = new ActorVerificationStructureBuilder(typeCtx)
  
  def translateEntity(actor: BasicActor): List[Boogie.Decl] = {
    val avs = actorVerStructBuilder.buildStructure(actor)
    translateActor(avs)
  }
  
    def translateActor(avs: ActorVerificationStructure): List[Boogie.Decl] = {    
    val decls = new ListBuffer[Boogie.Decl]()
    val actionFiringRules = collection.mutable.Map[AbstractAction,(Boogie.Expr,Boogie.Expr)]()
    val actionInpatDecls = collection.mutable.Map[AbstractAction,List[BDecl]]()
    val actionRenamings = collection.mutable.Map[AbstractAction,Map[String,Id]]()
    var allInpatDecls = Set.empty[BDecl]
    
    val bFunDecls = translateFunctionDecl(avs.functionDecls,avs.namePrefix)
    decls ++= bFunDecls
    
    decls += translateActorInit(avs)
    
    for (a <- avs.actorActions) {
      if (!a.init) {
        val (patterns,guards,inpatDecls,renamings) = translateGuards(a, avs)
        allInpatDecls = allInpatDecls ++ inpatDecls
        actionFiringRules += (a -> (patterns,guards))
        actionInpatDecls += (a -> inpatDecls)
        actionRenamings += (a -> renamings)
      }
    }
    
    for (a <- avs.actorActions) {
      if (!a.init) {
        val higherPrioActions = avs.priorityMap(a)
        val higherPrioGuards = higherPrioActions map { h => actionFiringRules(h) }
        decls ++= translateActorAction(a, avs, allInpatDecls.toList, avs.renamings ++ actionRenamings(a), actionFiringRules(a), higherPrioGuards)
      }
    }
    
    val allGuards = new ListBuffer[(AbstractAction,Boogie.Expr)]()
    //val supersetTests = new ListBuffer[Boogie.Expr]()
    
    for ((action,higherPrioActions) <- avs.priorityMap) {
      val (ownPattern,ownGuard) = actionFiringRules(action)
      val negHigherPrioGuards = higherPrioActions map { a => { val (p,g) = actionFiringRules(a); Boogie.UnaryExpr("!",p && g) } }

      val andedGuard = ownPattern && ownGuard
      
      val completeGuard = negHigherPrioGuards.foldLeft(B.Bool(true): Boogie.Expr)((g1,g2) => g1 && g2 ) && andedGuard
      allGuards += ((action,completeGuard))
    }
    
    if (!skipMutualExclusivenessCheck) {
      createMutualExclusivenessCheck(avs,allGuards.toList,allInpatDecls) match {
        case Some(proc) => decls += proc
        case None =>
      }
    }
    
    decls.toList
  }
  
  def createMutualExclusivenessCheck(
      avs: ActorVerificationStructure, guards: List[(AbstractAction,Boogie.Expr)], inpatDecls: Set[BDecl]): Option[Boogie.Proc] = {
    
    val nonInitActions = (avs.actorActions.filter { a => !a.init }).size
    
    if (nonInitActions > 1) {      
      val decls = 
        (avs.channelDecls map { _.decl }) ::: 
        (avs.actorVarDecls map { _.decl }) ::: 
        (inpatDecls map { _.decl }).toList ::: 
        List(B.Assume(avs.uniquenessCondition))
      
      val stmt = decls ::: createMEAssertionsRec(avs.entity,guards)
      Some(B.createProc(Uniquifier.get(avs.namePrefix+B.Sep+"GuardWD"), stmt, smokeTest))
    }
    else {
      None
    }
  }
  
  def createMEAssertionsRec(a: DFActor, guards: List[(AbstractAction,Boogie.Expr)]): List[Boogie.Assert] = {
    guards match {
      case (action1,first)::rest => {
        val asserts = for ((action2,guard) <- rest) yield {
          B.Assert(
              Boogie.UnaryExpr("!", first && guard) , a.pos, 
              "The actions '" + action1.fullName + "' and '" + action2.fullName + "' of actor '" + a.id + "' might not have mutually exclusive guards")
        }
        asserts:::createMEAssertionsRec(a,rest)
      }
      case Nil => Nil
    }
  }
  
  def translateActorInit(avs: ActorVerificationStructure) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)
    asgn ++= avs.initAssumes
    
//    if (ftMode) {
//      asgn += Boogie.Assign(B.SqnAct(B.This),B.Int(0))
//    }
    
    val initAction = avs.actorActions.find { x => x.init } 
    initAction match {
      case Some(a) => {
        asgn ++= transStmt( a.body )(avs.renamings)
        asgn ++= (for (q <- a.ensures) yield {
          B.Assert(transExpr(q)(avs.renamings), q.pos, "Action postcondition might not hold")
        })
     
        for (opat <- a.outputPattern) {
          val cId = opat.portId
          for (v <- opat.exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v)(avs.renamings))
            asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
          }
        }
      }
      case None =>
    }
    
    for (inv <- avs.invariants) {
      if (!inv.assertion.free) 
        asgn += B.Assert(transExpr(inv.expr)(avs.renamings),inv.expr.pos, "Initialization might not establish the invariant")
    }
    
    B.createProc(Uniquifier.get(avs.namePrefix+"init"),asgn.toList,smokeTest)
  }
  
  def translateGuards(a: ActorAction, avs: ActorVerificationStructure): (Boogie.Expr,Boogie.Expr,List[BDecl],Map[String,Id]) = {
    val renamingsBuffer = new ListBuffer[(String,Id)]
    val inpatDeclBuffer = new ListBuffer[BDecl]
    val patterns = new ListBuffer[Boogie.Expr]
    for (ipat <- a.inputPattern) {
      for ((v,i) <- ipat.vars.zipWithIndex) {
        val name = ipat.portId+B.Sep+i.toString
        renamingsBuffer += ((v.id, {val id = Id(name); id.typ = v.typ; id} ))
        val lVar = B.Local(name, v.typ)
        inpatDeclBuffer += BDecl(name,lVar)
      }
      patterns += B.Int(ipat.vars.size) <= B.C(ipat.portId)-B.R(ipat.portId)
    }
    val renamings = avs.renamings ++ renamingsBuffer.toMap
    val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExpr(e)(renamings))
       })
    val pattern = if (patterns.isEmpty) B.Bool(true) else patterns.reduceLeft((a,b) => a && b)
    val guard = if (guards.isEmpty) B.Bool(true) else guards.reduceLeft((a,b) => a && b)
    (pattern, guard, inpatDeclBuffer.toList, renamings)
  }
  
  def translateActorAction(
      a: ActorAction, 
      avs: ActorVerificationStructure,
      inpatDecls: List[BDecl],
      renamings: Map[String,Id], 
      guards: (Boogie.Expr,Boogie.Expr),
      higherPrioGuards: List[(Boogie.Expr,Boogie.Expr)]): List[Boogie.Decl] = {
     
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn ++= inpatDecls map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)
    
    if (a.init) asgn ++= avs.initAssumes
    else asgn ++= avs.basicAssumes
     
     if (!a.init) {
       // Assume invariants
       asgn ++= (for (i <- avs.invariants) yield B.Assume(transExpr(i.expr)(avs.renamings)))
     }
     
     val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExpr(e)(renamings))
       })
     
     for (ipat <- a.inputPattern) {
       val cId = ipat.portId
       
       for (v <- ipat.vars) {
         asgn += Boogie.Assign(transExpr(v)(renamings), B.ChannelIdx(cId, v.typ, B.R(cId)))
//         if (ftMode) asgn += Boogie.Assign(transExpr(v.id+"#sqn")(renamings), B.SqnCh(cId, B.R(cId)))
         asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
       }
     }
     
     asgn ++= (for (p <- a.requires) yield {B.Assume(transExpr(p)(renamings)) })
     
     asgn ++= higherPrioGuards map { case (pat,guard) => B.Assume(Boogie.UnaryExpr("!", pat && guard)) }
     
     asgn ++= guards map {g => B.Assume(g)}
     
     asgn ++= transStmt( a.body )(renamings)
     
     asgn ++= (for (q <- a.ensures) yield {
       B.Assert(transExpr(q)(renamings), q.pos, "Action postcondition might not hold")
     })
     
     for (opat <- a.outputPattern) {
       val cId = opat.portId
       for (v <- opat.exps) {
         asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v)(renamings))
//         if (ftMode) {
//           asgn += Boogie.Assign(B.SqnCh(cId, B.C(cId)), B.SqnAct(B.This))
//         }
         asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
         
       }
     }
     
//    if (ftMode) {
//      asgn += Boogie.Assign(B.SqnAct(B.This), B.SqnAct(B.This) plus B.Int(1))
//    }
     
     for (inv <- avs.invariants) {
       if (!inv.assertion.free) 
         asgn += B.Assert(transExpr(inv.expr)(avs.renamings),inv.expr.pos, "Action at " + a.pos + " might not preserve invariant")
     }
     
     val proc = B.createProc(Uniquifier.get(avs.namePrefix+a.fullName),asgn.toList,smokeTest)
     
     List(proc)
   }
  
  def translateFunctionDecl(funDecls: List[FunctionDecl], prefix: String): List[Boogie.Function] = {
    funDecls map {
      fd => {
        Boogie.Function(
            prefix+fd.name,
            fd.inputs map { i => Boogie.BVar(i.id, B.type2BType(i.typ)) },
            Boogie.BVar("out", B.type2BType(fd.output)))
      }
    }
  }
  
}

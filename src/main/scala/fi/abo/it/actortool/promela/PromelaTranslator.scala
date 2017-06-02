package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.promela.Promela.ChInit

class PromelaTranslator(params: CommandLineParameters) extends Translator[List[Promela.Decl]] {

  val P = Promela
  
  
  val charMapping = Map("$" -> "__", "#" -> "__") 
  
  def translateProgram(decls: List[TopDecl], typeCtx: Resolver.Context) = {
    
    val topNwName = params.Promela.get
    var program: Option[List[P.Decl]] = None
    for (d <- decls) {
      d match {
        case a: BasicActor => {
          //val proc = translateActor(a)
          //println(printer.print(proc))
        }
        case n: Network => {
          if (n.id == topNwName) {
            program = Some(translateTopNetwork(n))
          }
          else {
            // ..
          }
        }
        case _ =>
      }
    }
    program match {
      case Some(p) => p
      case None => throw new RuntimeException("Top-level network " + topNwName + " not found")
    }
  }
  
  def translateTopNetwork(nw: Network): List[P.Decl] = {
    val decls = new ListBuffer[P.VarDecl]
    val procs = new ListBuffer[P.ProcType]
    val instances = collection.mutable.Map[String,BasicActor]()
    val channelMapping = collection.mutable.Map[PortRef,Connection]()
    for (e <- nw.entities.get.entities) {
      e.actor match {
        case actor: BasicActor => 
          instances(e.id) = actor
          val proc = translateActor(actor)
          procs += proc
        case subnw: Network =>
          translateSubNetwork(subnw)
      }
    }
    for (c <- nw.structure.get.connections) {
      channelMapping(c.from) = c
      channelMapping(c.to) = c
      decls += P.VarDecl(rename(c.id), P.NamedType("chan"), Some(ChInit(100,translateType(c.typ.asInstanceOf[ChanType].contentType))))
    }
    
    val runs: List[P.Run] = {
      for ((i,a) <- instances.toList) yield {
        val params = 
          (a.inports map { ip => channelMapping(PortRef(Some(i),ip.id)).id }) ::: 
          (a.outports map { op => channelMapping(PortRef(Some(i),op.id)).id })
        
        P.Run(a.id, params map { p => P.VarExp(rename(p)) })
      }
    }
    
    val init = P.Init(List(P.Atomic(runs)))
    
    val program: List[P.Decl] = decls.toList ::: procs.toList ::: List(init)
    program
  }
  
  def translateSubNetwork(subNw: Network) = {
    for (e <- subNw.entities.get.entities) {
      e.actor match {
        case actor: BasicActor => translateActor(actor)
      }
    }
  }
  
  def translateActor(a: BasicActor): P.ProcType = {
    
    val params = new ListBuffer[P.ParamDecl]
    val decls = new ListBuffer[P.VarDecl]
    val actions = new ListBuffer[P.GuardStmt]
    
    for (ip <- a.inports) params += P.ParamDecl(ip.id,P.NamedType("chan"))
    for (op <- a.outports) params += P.ParamDecl(op.id,P.NamedType("chan"))
    for (v <- a.variables) decls += P.VarDecl(v.id,translateType(v.typ),None)
    
    val initStmts =
      a.actorActions.find { _.init } match {
        case Some(act) => translateStmts(act.body)
        case None => Nil
      }
    
    for (act <- a.actorActions.filter { !_.init }) {
      
      val stmt = new ListBuffer[P.Stmt]
      
      val inputRatePreds = act.inputPattern.map { ip => P.BinaryExpr(P.IntLiteral(ip.rate),"<=",P.FunCall("len",List(P.VarExp(ip.portId)))) }
      val inputPat = inputRatePreds.foldLeft(P.BoolLiteral(true): P.Expr)((a,b) => P.BinaryExpr(a,"&&",b))
      
      val firingRule = 
        if (act.guards.isEmpty) inputPat
        else P.BinaryExpr(inputPat,"&&",translateExpr(act.guards.reduceLeft((a,b) => And(a,b))) )
      
      for (p <- act.inputPattern) {
        for (v <- p.vars) {
          stmt += P.VarDecl(rename(v.id),translateType(v.typ),None)
        }
      }
        
      for (p <- act.inputPattern) {
        for (v <- p.vars) {
          stmt += P.Receive(rename(p.portId), translateExpr(v))
        }
      }
      
      stmt ++= translateStmts(act.body)
      
      for (p <- act.outputPattern) {
        for (e <- p.exps) {
          stmt += P.Send(rename(p.portId), translateExpr(e))
        }
      }
      
      actions += P.GuardStmt(firingRule, stmt.toList)
    }
    
    P.ProcType(a.id, params.toList,decls.toList,initStmts ::: List(P.Iteration(actions.toList)))
  }
  
  def translateStmts(stmt: List[Stmt]): List[P.Stmt] = {
    stmt map { s => translateStmt(s) }
  }
  
  def translateStmt(stmt: Stmt): P.Stmt = {
    stmt match {
      case Assign(i,e) => P.Assign(translateExpr(i),translateExpr(e))
    }
  }
  
  def translateExpr(e: Expr): P.Expr = {
    e match {
      case And(l,r) => P.BinaryExpr(translateExpr(l),"&&",translateExpr(r))
      case Plus(l,r) => P.BinaryExpr(translateExpr(l),"+",translateExpr(r))
      case Id(i) => {
        P.VarExp(rename(i))
      }
      case IntLiteral(i) => P.IntLiteral(i)
    }
  }
  
  def translateType(tp: Type): P.Type = {
    tp match {
      case IntType => P.NamedType("int")
    }
  }
  
  def rename(s: String) = charMapping.foldLeft(s)((a, b) => a.replaceAllLiterally(b._1, b._2))
  
}
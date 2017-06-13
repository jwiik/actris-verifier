package fi.abo.it.actortool.boogie

import scala.util.parsing.input.Position
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.boogie.Boogie.DeclComment
import fi.abo.it.actortool.boogie.Boogie.VarExpr
import fi.abo.it.actortool.boogie.Boogie.MapSelect
import fi.abo.it.actortool.boogie.Boogie.BType
import fi.abo.it.actortool.boogie.Boogie.NamedType
import fi.abo.it.actortool.boogie.Boogie.LocalVar
import fi.abo.it.actortool.boogie.Boogie.UnaryExpr
import fi.abo.it.actortool.ActorTool.TranslationException
import fi.abo.it.actortool._ 


abstract class EntityTranslator[T] {
  
  val stmtTranslator = new StmtExpTranslator();
  
  def translateEntity(entity: T): List[Boogie.Decl]
  
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
  
  def transSubActionFiringRules(
      instance: Instance, 
      action: AbstractAction, 
      nwvs: NetworkVerificationStructure) = {
    
    val firingCondsBuffer = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val renamings = nwvs.subActionRenamings(instance, action)
    val replacementMap = nwvs.getEntityActionData(instance,action).replacements
    
    for (ipat <- action.inputPattern) {
      val cId = nwvs.connectionMap.getDst(instance.id,ipat.portId)
      firingCondsBuffer += B.Int(ipat.rate) <= B.Urd(cId)
    }
    
    for (g <- action.guards) {
      val renamedGuard = IdReplacer.visitExpr(g)(replacementMap)
      val transGuard = transExpr(renamedGuard)(renamings)
      firingCondsBuffer += transGuard
    }
    
    firingCondsBuffer.reduceLeft((a,b) => a && b)
  }
  
  def transExprPrecondCheck(exp: Expr)(implicit renamings: Map[String,Expr]): Boogie.Expr = {
    val (expr,ctx) = stmtTranslator.transExpr(exp,renamings,true)
    expr
  }
  
  def transExpr(id: String, t: Type)(implicit renamings: Map[String,Expr]): Boogie.Expr = {
    val i = Id(id)
    i.typ = t
    transExpr(i)
  }
  
  def transExpr(exp: Expr)(implicit renamings: Map[String,Expr]): Boogie.Expr = {
    val (expr,ctx) = stmtTranslator.transExpr(exp,renamings,false)
    expr
  }
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,Expr]): List[Boogie.Stmt] = {
    val (bStmt,ctx) = stmtTranslator.transStmt(stmts,renamings,false)
    bStmt
  }
  
  def BAssume(chi: Invariant, renamings: Map[String,Expr]) = B.Assume(transExpr(chi.expr)(renamings))
  
  def BAssert(chi: Invariant, msg: String, renamings: Map[String,Expr]) = {
    val completeMsg = chi.assertion.msg match {
      case None => msg
      case Some(m) => msg + ": " + m
    }
    B.Assert(transExpr(chi.expr)(renamings), chi.expr.pos, completeMsg)
  }
  
  
}

class Translator( 
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean) extends Backend[List[Boogie.Decl]] {  
  
  
  def invoke(programCtx: ProgramContext): List[Boogie.Decl] = {
    val typeCtx = programCtx.typeContext
    assert(typeCtx.getErrors.isEmpty)
    
    val stmtTranslator = new StmtExpTranslator();
    
    lazy val actorTranslator = new BasicActorTranslator(smokeTest,skipMutualExclusivenessCheck,typeCtx)
    lazy val networkTranslator = new NetworkTranslator(smokeTest,skipMutualExclusivenessCheck,typeCtx)
    
    val bProgram = programCtx.program flatMap {
      case a: BasicActor => actorTranslator.translateEntity(a)
      case n: Network => networkTranslator.translateEntity(n)
      case u: DataUnit => {
        u.constants flatMap { d =>
          val (axiom,_) = stmtTranslator.transExpr(d.value.get,Map.empty,false)
          List(Boogie.Const(d.id,false,B.type2BType(d.typ)),Boogie.Axiom(Boogie.VarExpr(d.id) ==@ axiom))
        }
      }
      case td: TypeDecl => {
        //userTypes += (td.tp.id -> NamedType(td.tp.id))
        for (f <- td.fields) yield {
          Boogie.Const(td.tp.id+"."+f.id,true,BType.Field(B.type2BType(f.typ)))
        }
      }
    }
    
    return bProgram
    
  }

}

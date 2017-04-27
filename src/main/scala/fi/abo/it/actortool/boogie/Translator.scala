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


abstract class EntityTranslator[T <: DFActor] {
  
  val stmtTranslator = new StmtExpTranslator();
  
  def translateEntity(entity: T): List[Boogie.Decl]
  
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
    val skipMutualExclusivenessCheck: Boolean) {  
  
  
  def translateProgram(decls: List[TopDecl], typeCtx: Resolver.Context): List[Boogie.Decl] = {
    assert(typeCtx.getErrors.isEmpty)
    
    lazy val actorTranslator = new BasicActorTranslator(smokeTest,skipMutualExclusivenessCheck,typeCtx)
    lazy val networkTranslator = new NetworkTranslator(smokeTest,skipMutualExclusivenessCheck,typeCtx)
    
    val bProgram = decls flatMap {
      case a: BasicActor => actorTranslator.translateEntity(a)
      case n: Network => networkTranslator.translateEntity(n)
      case u: DataUnit => Nil
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

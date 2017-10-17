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


case class GuardTranslation(
    val action: AbstractAction,
    val declarations: Seq[BDecl],
    val renamings: Map[String,Id],
    val pattern: Boogie.Expr,
    val localGuard: Boogie.Expr,
    val nonLocalGuard: Boogie.Expr)

case class BoogieTranslation[T](val entity: T, program: Seq[Boogie.Decl])
    
abstract class EntityTranslator[T,U] {
  
  val stmtTranslator = new StmtExpTranslator();
  
  def translateEntity(entity: T): Seq[BoogieTranslation[U]]
  
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
      acvs: SubActionVerStruct) = {
    
    val firingCondsBuffer = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    //val renamings = nwvs.subActionRenamings(instance, action)
    val renamings = acvs.renamings
    val replacementMap = acvs.replacements
    
    for (ipat <- action.inputPattern) {
      val cId = acvs.connectionMap.getDst(instance.id,ipat.portId)
      firingCondsBuffer += B.Int(ipat.rate) <= B.Urd(cId)
    }
    
    for (g <- action.guards) {
      val renamedGuard = IdReplacer.visitExpr(g)(replacementMap)
      val transGuard = transExpr(renamedGuard,acvs)
      firingCondsBuffer += transGuard
    }
    
    firingCondsBuffer.reduceLeft((a,b) => a && b)
  }
  
  def translateActorGuards(a: ActorAction, avs: RootVerStruct[BasicActor]): GuardTranslation = {
    val renamingsBuffer = new ListBuffer[(String,Id)]
    
    val replacementBuffer = new ListBuffer[(String,Expr)]
    
    val inpatDeclBuffer = new ListBuffer[BDecl]
    val patterns = new ListBuffer[Boogie.Expr]
    for (ipat <- a.inputPattern) {
      if (ipat.repeat == 1) {
        for ((v,i) <- ipat.vars.zipWithIndex) {
          val name = ipat.portId+B.Sep+i.toString
          renamingsBuffer += ((v.id, Id(name).withType(v.typ) ))
          replacementBuffer += (( 
              v.id, 
              Elements.next(ipat.portId, ChanType(v.typ), i).withType(v.typ) 
          ))
          val lVar = B.Local(name, v.typ)
          inpatDeclBuffer += BDecl(name,lVar)
        }
      }
      else {
        val v = ipat.vars(0)
        val name = ipat.portId+B.Sep+"0"
        renamingsBuffer += ((v.id, Id(name).withType(v.typ) ))
        replacementBuffer += (( 
              v.id, 
              Elements.chAcc(Elements.ch(ipat.portId,v.typ), Elements.next(ipat.portId, ChanType(v.typ), 0)).withType(v.typ) 
          ))
        val lVar = B.Local(name, v.typ)
        inpatDeclBuffer += BDecl(name,lVar)
      }
      patterns += B.Int(ipat.rate) <= B.C(ipat.portId)-B.R(ipat.portId)
    }
    
    val renamings = avs.renamings ++ renamingsBuffer.toMap

    val transCtx = TranslatorContext(avs.renamings ++ renamingsBuffer.toMap, false)
    
    val guards =
       a.guards map { e =>  stmtTranslator.transExpr(e, TranslatorContext(avs.renamings ++ renamingsBuffer.toMap, false))  }
    // This version does not use variables local to the actions (input pattern variables)
    // It is used (at least) as assumptions in contract action checking
    val nonLocalGuards =
       a.guards map { e => stmtTranslator.transExpr(e, TranslatorContext(avs.renamings ++ replacementBuffer.toMap,false)) }
    
    val pattern = if (patterns.isEmpty) B.Bool(true) else patterns.reduceLeft((a,b) => a && b)
    val guard = if (guards.isEmpty) B.Bool(true) else guards.reduceLeft((a,b) => a && b)
    val nonLocalGuard = if (nonLocalGuards.isEmpty) B.Bool(true) else nonLocalGuards.reduceLeft((a,b) => a && b)
    
    GuardTranslation(a,inpatDeclBuffer.toSeq,renamingsBuffer.toMap,pattern,guard,nonLocalGuard)
  }
  
  def translateFunctionDecl(vs: ActorVerStruct): List[Boogie.Function] = {
    vs.entity.functionDecls map {
      fd => {
        Boogie.Function(
            vs.renamings(fd.name).id,
            fd.inputs map { i => Boogie.BVar(i.id, B.type2BType(i.typ)) },
            Boogie.BVar("out", B.type2BType(fd.output)))
      }
    }
  }
  
  def generateHavoc[T<:Assignable](assignables: Set[T], vs: VerStruct[_]) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    for (ev <- assignables) {
      val hVar = Boogie.VarExpr(BMap.H)
      val qF = Boogie.VarExpr("f$")
      val qR = Boogie.VarExpr("r$")
      val qVars =
          List(Boogie.BVar("r$", BType.Ref),Boogie.BVar("f$", BType.ParamField("a")))
      val qExp1 = 
        hVar.apply(qR).apply(qF) ==@ Boogie.Old(hVar).apply(qR).apply(qF)
      
      ev match {
        case fa@FieldAccessor(r,f) => {
          val fieldName = B.FieldName(r.typ.asInstanceOf[RefType].name, f);
          val qExp2 = ((qR ==@ transExpr(r,vs)) && (qF ==@ Boogie.VarExpr(fieldName)))
          val frameCond = Boogie.Forall(List(Boogie.TVar("a")),qVars,Nil, (qExp1 || qExp2) )
          asgn += Boogie.Havoc(hVar)
          asgn += B.Assume(frameCond)
        }
        case id: Id => {
          if (id.typ.isRef) {
            val qExp2 = qR ==@ transExpr(id,vs)
            val frameCond = Boogie.Forall(List(Boogie.TVar("a")),qVars,Nil,qExp1 || qExp2)
            asgn += Boogie.Havoc(hVar)
            asgn += B.Assume(frameCond)
          }
          else {
            asgn += Boogie.Havoc(transExpr(ev,vs)) 
          }
        }
        case IndexAccessor(v,_) => {
          asgn += Boogie.Havoc(transExpr(v,vs)) 
          //throw new TranslationException(ev.pos, "")
        }
      }
    }
    asgn.toList
  }
  
  def transExprPrecondCheck(exp: Expr, vs: VerStruct[_]): Boogie.Expr = {
    val ctx = TranslatorContext(vs.renamings,true,vs.stateChannelNames)
    stmtTranslator.transExpr(exp,ctx)
  }
  
  def transExpr(id: String, tp: Type, vs: VerStruct[_]): Boogie.Expr = {
    val i = Id(id)
    i.typ = tp
    transExpr(i,vs)
  }
  
  def transExpr(exp: Expr, vs: VerStruct[_]): Boogie.Expr = {
    val ctx = TranslatorContext(vs.renamings,false,vs.stateChannelNames)
    stmtTranslator.transExpr(exp,ctx)
  }
  
  def transStmt(stmts: List[Stmt], vs: VerStruct[_]): List[Boogie.Stmt] = {
    val ctx = TranslatorContext(vs.renamings,false,vs.stateChannelNames)
    stmtTranslator.transStmt(stmts,ctx)
  }
  
  def BAssume(chi: Invariant, vs: VerStruct[_]) = B.Assume(transExpr(chi.expr,vs))
  
  def BAssert(chi: Invariant, msg: String, vs: VerStruct[_]) = {
    val completeMsg = chi.assertion.msg match {
      case None => msg
      case Some(m) => msg + ": " + m
    }
    B.Assert(transExpr(chi.expr,vs), chi.expr.pos, completeMsg)
  }
  
  
}

class Translator( 
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    val actorActionsOnly: Boolean) extends Backend[Seq[BoogieTranslation[_<:TopDecl]]] {  
  
  
  def invoke(programCtx: ProgramContext): Seq[BoogieTranslation[_<:TopDecl]] = {
    val typeCtx = programCtx.typeContext
    assert(typeCtx.getErrors.isEmpty)
    
    val stmtTranslator = new StmtExpTranslator();
    
    lazy val actorTranslator = new BasicActorTranslator(smokeTest,skipMutualExclusivenessCheck,typeCtx,!actorActionsOnly)
    lazy val networkTranslator = new NetworkTranslator(smokeTest,skipMutualExclusivenessCheck,typeCtx,true)
    
    val bProgram = programCtx.program flatMap {
      case a: BasicActor => actorTranslator.translateEntity(a)
      case n: Network => if (!actorActionsOnly) networkTranslator.translateEntity(n) else Seq.empty
      case u: DataUnit => {
        Seq(BoogieTranslation(
            u,
            u.constants flatMap { d =>
              val axiom = stmtTranslator.transExpr(d.value.get,false)
              List(Boogie.Const(d.id,false,B.type2BType(d.typ)),Boogie.Axiom(Boogie.VarExpr(d.id) ==@ axiom))
            }))
      }
      case td: TypeDecl => {
        //userTypes += (td.tp.id -> NamedType(td.tp.id))
        Seq(BoogieTranslation(
            td,
            for (f <- td.fields) yield {
              Boogie.Const(td.tp.id+"."+f.id,true,BType.Field(B.type2BType(f.typ)))
            }))
      }
    }
    
//    println(bProgram.size)
//    for (p <- bProgram) {
//      println(p.entity.id)
//    }
    return bProgram
    
  }

}

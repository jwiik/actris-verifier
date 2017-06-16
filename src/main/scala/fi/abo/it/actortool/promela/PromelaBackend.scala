package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.merging.ActorMerger
import fi.abo.it.actortool.boogie.BoogieScheduleVerifier

class PromelaBackend(val params: CommandLineParameters) extends Backend[BasicActor] {
  
  val printer = new Promela.PromelaPrinter
  
  
  def invoke(programCtx: ProgramContext): BasicActor = {
    val translator = new PromelaTranslator(params)
    val scheduleVerifier = new BoogieScheduleVerifier(params)
    
    val topNwName = params.Promela.get
    val topnw = programCtx.program.find { x => x.id == topNwName }
    val allSchedules = new collection.mutable.ListBuffer[ContractSchedule]
    
    val constants = (programCtx.program.collect { case DataUnit(_,constants) => constants }).flatten
    val mergerBackend = new ActorMerger(constants)
    topnw match {
      case Some(nw) => {
        val evaluationOrder = buildDependencyTree(nw.asInstanceOf[DFActor]).postOrder
        //println(evaluationOrder map { _.id })
        val mergedActorMap = collection.mutable.Map[String,BasicActor]()
        for (entity <- evaluationOrder) {
          entity match {
            case ba: BasicActor => {
              if (entity.contractActions.isEmpty) mergedActorMap += (entity.id -> ba)
              else {
                val translation = translator.invoke(ba,mergedActorMap.toMap,Map.empty,constants)
                val outputParser = new SpinOutputParser(translation)
                for ((contract,prog) <- translation.promelaPrograms) {
                  verifyForContract(translation.entity, contract, prog,outputParser)
                }
                val schedules = outputParser.allSchedules
                
                scheduleVerifier.invoke(new ScheduleContext(schedules,programCtx.program,programCtx.typeContext))
                val actor = mergerBackend.invoke(schedules)
                actor match {
                  case Some(a) => mergedActorMap += (entity.id -> a)
                  case None => assert(false)
                }
                //mergedActorMap += (entity.id -> actor)
              }
            }
            case nw: Network => {
              val translation = translator.invoke(nw,mergedActorMap.toMap,Map.empty,constants)
              val outputParser = new SpinOutputParser(translation)
              for ((contract,prog) <- translation.promelaPrograms) {
                verifyForContract(translation.entity, contract, prog,outputParser)
              }
              val schedules = outputParser.allSchedules
              println("Verifying obtained schedule...")
              scheduleVerifier.invoke(new ScheduleContext(schedules,programCtx.program,programCtx.typeContext))
              println
              val actor = mergerBackend.invoke(schedules)
              actor match {
                case Some(a) => mergedActorMap += (entity.id -> a)
                case None => assert(false)
              }
              //mergedActorMap += (entity.id -> actor)
            }
          }
        }
        println("Merging successful\n")
        mergedActorMap(topNwName)
      }
      case None => throw new RuntimeException("There is no network named " + topNwName)
    }
//    val translator = new PromelaTranslator(params)
//    val translations = translator.invoke(programCtx)
//    translations.flatMap { t =>
//      val outputParser = new SpinOutputParser(t)
//      for ((contract,prog) <- t.promelaPrograms) {
//        verifyForContract(t.network, contract, prog,outputParser)
//      }
//      outputParser.allSchedules
//    }
  }
  
  def verifyForContract[T<:DFActor](entity: T, contract: ContractAction, promelaProg: List[Promela.Decl], outputParser: SpinOutputParser) = {
    val progTxt = PromelaPrelude.get + promelaProg.map(printer.print).foldLeft("")((a,b) => a + b)
    if (params.PromelaPrint) {
      println(progTxt)
    }
    outputParser.startNewSchedule(contract)
    println("Running spin on contract '" + contract.fullName + "' of network '" + entity.id + "'...")
    PromelaRunner.run(progTxt, entity.id + "__" + contract.fullName+".pml", outputParser)
    outputParser.endSchedule
  }
  
  def buildDependencyTree(entity: DFActor): DepTree[DFActor] = {
    entity match {
      case nw: Network => {
        val entities = nw.entities.get.entities
        val children = for (e <- entities) yield buildDependencyTree(e.actor)
        if (children.isEmpty) Leaf(nw) else Branch(nw,children)
      }
      case ba: BasicActor => Leaf(ba)
    }
  }
  
}

sealed trait DepTree[+A<:DFActor] {
  def value: A
  def postOrder: List[A]
}
case class Leaf[A<:DFActor](val value: A) extends DepTree[A] {
  override def toString = "Leaf(" + value.id +")"
  def postOrder = List(value)
}
case class Branch[A<:DFActor](val value: A, val children: List[DepTree[A]]) extends DepTree[A] {
  override def toString = "Branch(" + value.id +","+ children.toString +")"
  def postOrder = children.flatMap { _.postOrder } ::: List(value)
}

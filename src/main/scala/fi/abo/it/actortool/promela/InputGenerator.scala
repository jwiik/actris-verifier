package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import fi.abo.it.actortool.z3._

class InputGenerator {
  
  def generateInput(contract: ContractAction, constants: List[Declaration]): Map[String,List[Expr]] = {
    var declarations = List.empty[Declaration]
    var portId = Map.empty[String,Int]
    var id = 0
    for (pat <- contract.inputPattern) {
      portId += (pat.portId -> id)
      declarations = Declaration(pat.portId,pat.typ,true,Some(IntLiteral(id))) :: declarations
      id += 1
    }
    for (pat <- contract.outputPattern) {
      portId += (pat.portId -> id)
      declarations = Declaration(pat.portId,pat.typ,true,Some(IntLiteral(id))) :: declarations
      id += 1
    }
    
    val checker = new fi.abo.it.actortool.z3.Checker 
    val result = checker.getSatisfyingModel(contract.guards ::: contract.requires ::: contract.ensures, declarations, constants)
    
    queryModel(contract, result, portId)
    
//    val names = collection.mutable.Map[(String,Int),String]()
//    val reverseNames = collection.mutable.Map[String,(String,Int)]()
//    val types = collection.mutable.Map[String,Type]()
//    for (pat <- contract.inputPattern) {
//      val name = pat.portId
//      names((pat.portId,0)) = name
//      reverseNames(name) = (pat.portId,0)
//      types(name) = pat.typ
////      for (i <- 0 to pat.rate-1) {
////        val name = pat.portId + "#" + i
////        names((pat.portId,i)) = name
////        reverseNames(name) = (pat.portId,i)
////        types(name) = pat.typ
////      }
//    }
//    for (pat <- contract.outputPattern) {
//      val name = pat.portId
//      names((pat.portId,0)) = name
//      reverseNames(name) = (pat.portId,0)
//      types(name) = pat.typ
////      for (i <- 0 to pat.rate-1) {
////        val name = pat.portId + "#" + i
////        names((pat.portId,i)) = name
////        reverseNames(name) = (pat.portId,i)
////        types(name) = pat.typ
////      }
//    }
//    val checker = new fi.abo.it.actortool.z3.Checker 
//    val result = checker.getSatisfyingModel(contract.guards ::: contract.requires ::: contract.ensures, constants, names.toMap, types.toMap)
//    
//    val values = collection.mutable.Map[(String,Int),Expr]()
//    for (n <- reverseNames.keys) {
//      val tp = types(n)
//      val token = reverseNames(n)
//      tp match {
//        case IntType => result.getResultInt(n) match {
//          case Some(i) => values(token) =  IntLiteral(i)
//          case None => throw new RuntimeException( n )
//        }
//        case BvType(size,_) => result.getResultHex(n) match {
//          case Some(i) => values(token) = IntLiteral(i)
//          case None => throw new RuntimeException( n )
//        }
//      }
//    }
//    println(values)
//    values.toMap
  }
  
  def queryModel(contract: ContractAction, result: Result, portId: Map[String,Int]): Map[String,List[Expr]] = {
    val (iRaw,iDef) = result.getFunctionInterpretation("I#").get
    val (mRaw,mDef) = result.getFunctionInterpretation("M#").get
    val iMap = {
      for ((k,v) <- portId) yield {
        val value = v.toString
        val interpret =
          iRaw.find {
            case (dom,rng) => dom(0).toString == value
          }
        (k, interpret.get._2.toString.toInt)
      }
    }.toMap
    val mMap = {
      (for (pat <- contract.inputPattern) yield {
        val pId = portId(pat.portId)
        val iPos = iMap(pat.portId)
        val map =
          (for (i <- (0 to pat.rate-1)) yield {
            val pos = iPos + i
            val interpret =
              mRaw.find {
                case (dom,rng) => dom(0).toString == pId.toString && dom(1).toString == pos.toString
              }
            interpret match {
              case Some(vl) => IntLiteral(vl._2.toString.toInt)
              case None => IntLiteral(mDef.toString.toInt)
            }
          }).toList
        (pat.portId -> map)
      }).toMap
    }
    mMap
  }
  
}


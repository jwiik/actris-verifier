package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import fi.abo.it.actortool.z3._
import fi.abo.it.actortool.ActorTool.TranslationException

class InputGenerator {
  
  def generateInput(contract: ContractAction, constants: Seq[Declaration]): Map[String,List[Expr]] = {
    var declarations = List.empty[Declaration]
    var portIdDeclarations = List.empty[Declaration]
    var portId = Map.empty[String,Int]
    var id = 0
    for (pat <- contract.inputPattern) {
      portId += (pat.portId -> id)
      declarations = Declaration("M#"+pat.portId,pat.typ,true,None) :: declarations
      portIdDeclarations = Declaration(pat.portId,IntType,true,Some(IntLiteral(id))) :: portIdDeclarations
      id += 1
    }
    for (pat <- contract.outputPattern) {
      portId += (pat.portId -> id)
      declarations = Declaration("M#"+pat.portId,pat.typ,true,None) :: declarations
      portIdDeclarations = Declaration(pat.portId,IntType,true,Some(IntLiteral(id))) :: portIdDeclarations
      id += 1
    }
    
    val checker = new fi.abo.it.actortool.z3.Checker 
    val result = checker.getSatisfyingModel(contract.guards ::: contract.requiresExpr ::: contract.ensuresExpr, declarations, portIdDeclarations, constants)
    
    val inputSeqs = queryModel(contract, result, portId)
    //println(contract.fullName + ": " +inputSeqs)
    inputSeqs
  }
  
  def queryModel(contract: ContractAction, result: Result, portId: Map[String,Int]): Map[String,List[Expr]] = {
    
    val (iRaw,iDef) = result.getFunctionInterpretation("I#").get
    //val (mRaw,mDef) = result.getFunctionInterpretation("M#").get
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
    val input =
      for (pat <- contract.inputPattern ::: contract.outputPattern) yield {
        val iPos = iMap(pat.portId)
        val func = result.getFunctionInterpretation("M#"+pat.portId)
        if (func.isDefined) {
          val (mRaw,mDef) = func.get
          val seq =
            (for (i <- (0 to pat.rate-1)) yield {
              val pos = iPos + i
              val interpret =
                mRaw.find {
                  case (dom,rng) => dom(0).toString == pos.toString
                }
              interpret match {
                case Some(vl) => {
                  val value = vl._2.toString
                  val dec = getValue(value)
                  dec
                }
                case None => getValue(mDef.toString)
              }
            }).toList
          (pat.portId -> seq)
        }
        else {
          val default: Expr = getDefault(pat.typ)
          
          (pat.portId -> (for (i <- (0 to pat.rate-1)) yield default).toList)
        }
      }
    input.toMap
  }
  
  def getValue(value: String) = {
    var v = value
    if (v.startsWith("(") && v.endsWith(")")) {
      v = v.substring(1, v.length-1)
    }
    
    if (v.startsWith("#b")) {
      val v2 = get2Complement(value.substring(2))
      if (v2 < 0) UnMinus(IntLiteral(-v2)) else IntLiteral(v2)
    }
    else if (v.startsWith("#x")) HexLiteral(v.substring(2))
    else {
      if (v.startsWith("- ")) {
        var c = v.substring(2)
        UnMinus(IntLiteral(c.toInt))
      }
      else IntLiteral(v.toInt)
    }
  }
  
  def getDefault(typ: Type) = {
    typ match {
      case IntType(_) => IntLiteral(0)
      case UintType(_) => IntLiteral(0)
      case BvType(_,_) => HexLiteral("0")
      case BoolType => BoolLiteral(false)
      case _ => throw new TranslationException(typ.pos,"Unsupported type for Z3 backend")
    }
  }
  
  def get2Complement(binary: String) = {
    if (binary.charAt(0) == '1') {
      val inverted = binary.replace("0"," ").replace("1", "0").replace(" ","1")
      val decimal = Integer.parseInt(inverted,2)
      (decimal+1) * (-1)
    }
    else {
      Integer.parseInt(binary,2)
    }
  }
  
}


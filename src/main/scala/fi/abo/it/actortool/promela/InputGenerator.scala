package fi.abo.it.actortool.promela

import fi.abo.it.actortool._

class InputGenerator {
  
  def generateInput(contract: ContractAction, constants: List[Declaration]): Map[(String,Int),Expr] = {
    val inputNames = collection.mutable.Map[(String,Int),String]()
    val reverseInputNames = collection.mutable.Map[String,(String,Int)]()
    val inputTypes = collection.mutable.Map[String,Type]()
    for (pat <- contract.inputPattern) {
      for (i <- 0 to pat.rate-1) {
        val name = pat.portId + "#" + i
        inputNames((pat.portId,i)) = name
        reverseInputNames(name) = (pat.portId,i)
        inputTypes(name) = pat.typ
      }
    }
    val checker = new fi.abo.it.actortool.z3.Checker 
    val result = checker.getSatisfyingModel(contract.guards ::: contract.requires, constants, inputNames.toMap, inputTypes.toMap)
    
    val inputValues = collection.mutable.Map[(String,Int),Expr]()
    for (n <- reverseInputNames.keys) {
      val tp = inputTypes(n)
      val token = reverseInputNames(n)
      tp match {
        case IntType => result.getResultInt(n) match {
          case Some(i) => inputValues(token) =  IntLiteral(i)
          case None => throw new RuntimeException( n )
        }
        case BvType(size,_) => result.getResultHex(n) match {
          case Some(i) => inputValues(token) = IntLiteral(i)
          case None => throw new RuntimeException( n )
        }
      }
    }
    
    inputValues.toMap
  }
  
}
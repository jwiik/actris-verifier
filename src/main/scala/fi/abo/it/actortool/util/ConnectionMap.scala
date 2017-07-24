package fi.abo.it.actortool.util

import fi.abo.it.actortool._

trait ConnectionMap {
  def getSrc(pr: PortRef): String
  def getDst(pr: PortRef): String
  def getSrc(instance: String, port: String): String
  def getDst(instance: String, port: String): String
  def getIn(port: String): String
  def getOut(port: String): String
  def connections: List[Connection]
}

class ConnectionMapImpl(srcMap: Map[PortRef,String], trgtMap: Map[PortRef,String], conns: List[Connection]) extends ConnectionMap {
  def getSrc(pr: PortRef) = srcMap(pr)
  def getDst(pr: PortRef) = trgtMap(pr)
  def getSrc(instance: String, port: String) = srcMap(PortRef(Some(instance),port))
  def getDst(instance: String, port: String) = trgtMap(PortRef(Some(instance),port))
  def getIn(port: String) = srcMap(PortRef(None,port))
  def getOut(port: String) = trgtMap(PortRef(None,port))
  def connections = conns
}

object ConnectionMap {
  def build(connections: List[Connection], renames: Map[String,Id]): ConnectionMap = {
    val source = scala.collection.mutable.HashMap.empty[PortRef,String]
    val target = scala.collection.mutable.HashMap.empty[PortRef,String]
    for (c <- connections) {
      source(c.from) = renames.get(c.id) match {
        case Some(id) => id.id
        case None => c.id
      }
      target(c.to) = renames.get(c.id) match {
        case Some(id) => id.id
        case None => c.id
      }
    }
    new ConnectionMapImpl(source.toMap,target.toMap, connections)
  }
  
  def empty = new ConnectionMapImpl(Map.empty,Map.empty,List.empty)
}
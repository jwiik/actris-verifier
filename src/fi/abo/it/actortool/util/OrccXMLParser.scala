package fi.abo.it.actortool.util

import scala.xml.XML

object OrccXMLParser {
  
  def run = {
    val buffer = new StringBuilder
    val filePath = "orcc/LMS_lowlevel.xdf"
    val xml = XML.loadFile(filePath)
    
    val instances = xml \ "Instance"
    val connections = xml \ "Connection"
    buffer ++= "network\n"
    buffer ++= "  entities\n"
    for (instance <- instances) {
      val id = instance \ "@id"
      val cl = instance \ "Class" \ "@name"
      buffer ++= "    " + id + " = " + cl + "("  + ");\n"
    }
    buffer ++= "  end\n"
    
    buffer ++= "  structure\n"
    for (con <- connections) {
      val dst = con \ "@dst"
      val dst_port = con \ "@dst-port"
      val src = con \ "@src"
      val src_port = con \ "@src-port"
      buffer ++= "    " + src + "." + src_port + " --> " + dst + "." + dst_port + ";\n"
    }
    buffer ++= "  end\n"
    buffer ++= "end\n"
    println(buffer.toString)
  }
  
}
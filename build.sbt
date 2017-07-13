name := "actris"
organization := "fi.abo.it"
version := "0.3.0a"
scalaVersion := "2.11.8"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.5"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"
libraryDependencies += "org.scala-lang.modules" % "scala-xml_2.11" % "1.0.6"

packSettings
packMain := Map("actris" -> "fi.abo.it.actortool.ActorTool")
packJvmOpts := Map("actris" -> Seq("-Djava.library.path=\"/usr/local/lib\""))

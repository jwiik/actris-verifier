lazy val commonSettings = Seq(
  name := "actortool",
  version := "0.1.0",
  organization := "fi.abo.it",
  scalaVersion := "2.11.7"
)

lazy val root = 
  (project in file(".")).
  settings(commonSettings: _*)

scalaSource in Compile := baseDirectory.value / "src"




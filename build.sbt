lazy val commonSettings = Seq(
  name := "actris",
  version := "0.2.0",
  organization := "fi.abo.it",
  scalaVersion := "2.11.7"
)

lazy val root = 
  (project in file(".")).
  settings(commonSettings: _*)

scalaSource in Compile := baseDirectory.value / "src"




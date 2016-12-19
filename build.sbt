lazy val root = 
  (project in file(".")).
  settings(
    name := "actortool",
    version := "0.1.0",
    scalaVersion := "2.11.7"
  )

scalaSource in Compile := baseDirectory.value / "src"
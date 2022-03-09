ThisBuild / scalaVersion := "2.12.14"
lazy val silicon = (project in file("silicon"))
lazy val gvc = (project in file("."))
  .settings(
    name := "gvc0",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % Test,
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.3.3"
  )
  .dependsOn(silicon)
Compile / run / fork := true
Compile / run / javaOptions += "-Xss15m"
parallelExecution in Test := false
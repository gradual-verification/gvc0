ThisBuild / scalaVersion := "2.12.14"

lazy val silver = project in file("silver")
lazy val silicon = project in file("silicon")

lazy val gvc = (project in file("."))
  .settings(
    name := "gvc0",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % Test,
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.2.2",
  )
  .dependsOn(silver)
  .dependsOn(silicon)
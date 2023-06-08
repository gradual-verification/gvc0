ThisBuild / scalaVersion := "2.12.14"

lazy val silicon = (project in file("silicon"))

lazy val gvteal = (project in file("."))
  .settings(
    name := "gvc0",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % Test,
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.3.3",
    libraryDependencies += "org.tpolecat" %% "doobie-core" % "1.0.0-RC1",
    libraryDependencies += "org.tpolecat" %% "doobie-h2" % "1.0.0-RC1", // H2 driver 1.4.199 + type mappings.
    libraryDependencies += "org.tpolecat" %% "doobie-hikari" % "1.0.0-RC1", // HikariCP transactor.
    libraryDependencies += "mysql" % "mysql-connector-java" % "8.0.29",
    Test / testOptions +=
      Tests.Argument(
        TestFrameworks.ScalaTest,
        "-Dclasspath=" + (Runtime / fullClasspath).value.files.mkString(":")
      )
  )
  .dependsOn(silicon)
Compile / run / fork := true
Compile / run / javaOptions += "-Xss15m"
assembly / assemblyMergeStrategy := {
  case PathList("META-INF", xs @ _*) => MergeStrategy.discard
  case x                             => MergeStrategy.first
}

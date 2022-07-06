ThisBuild / scalaVersion := "2.12.14"

lazy val silicon = (project in file("silicon"))

lazy val gvc = (project in file("."))
  .settings(
    name := "gvc0",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % Test,
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.3.3",
    libraryDependencies += "org.tpolecat" %% "doobie-core" % "1.0.0-RC1",
    libraryDependencies += "org.tpolecat" %% "doobie-postgres" % "1.0.0-RC1", // Postgres driver 42.3.1 + type mappings.
    libraryDependencies += "io.spray" %% "spray-json" % "1.3.6",
    Test / testOptions +=
      Tests.Argument(
        TestFrameworks.ScalaTest,
        "-Dclasspath=" + (Runtime / fullClasspath).value.files.mkString(":")
      )
  )
  .dependsOn(silicon)
Compile / run / fork := true
Compile / run / javaOptions += "-Xss15m"

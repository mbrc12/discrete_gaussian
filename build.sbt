val scala3Version = "3.1.1"

lazy val root = project
  .in(file("."))
  .settings(
    name := "dg",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    /* libraryDependencies += "org.scalameta" %% "munit" % "0.7.29" % Test, */
    libraryDependencies += "org.jfree" % "jfreesvg" % "3.4.2"
    /* libraryDependencies += "org.typelevel" %% "cats-effect" % "3.3.8" */
  )

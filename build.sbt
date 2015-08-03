name := "graph-rewriting"

organization := "uk.ac.ed.inf"

version := "0.2"

scalaVersion := "2.11.6"

resolvers += "Sonatype snapshots" at
  "https://oss.sonatype.org/content/repositories/snapshots/"

val scalajs = false

if (scalajs) {
  enablePlugins(ScalaJSPlugin);
  // ScalaTest hasn't been ported yet to Scala.js
  // libraryDependencies += "org.scalatest" %%% "scalatest_2.11" % "2.2.4" % "test"
} else {
  libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.4" % "test"
}


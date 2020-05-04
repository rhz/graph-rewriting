name := "graph-rewriting"
organization := "hz.ricardo"
version := "0.3"
scalaVersion := "2.13.2"
// scalacOptions ++= Seq("-deprecation", "-feature")

libraryDependencies +=
  "org.scalatest" %%% "scalatest" % "3.1.1" % "test"

val scalajs = false
if (scalajs) {
  enablePlugins(ScalaJSPlugin)
} else {
  libraryDependencies += "com.storm-enroute" %%% "scalameter" % "0.19"
}

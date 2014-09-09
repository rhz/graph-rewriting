name := "graph-rewriting"

version := "0.1"

scalaVersion := "2.10.4" // "2.11.1"

resolvers += "ScalaTools snapshots at Sonatype" at "https://oss.sonatype.org/content/repositories/snapshots/"

libraryDependencies ++= Seq(
  "org.scalatest" % "scalatest_2.10" % "2.1.5" % "test",
  "com.assembla.scala-incubator" % "graph-core_2.10" % "1.8.1"
)

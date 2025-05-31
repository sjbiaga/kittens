import Dependencies._

ThisBuild / scalaVersion := "3.7.1-RC2"

Global / resolvers += "scala-integration" at "https://scala-ci.typesafe.com/artifactory/scala-integration/"

val scala2Opts = Seq("-feature", "-language:implicitConversions", "-deprecation", "-Ytasty-reader")
val scala3Opts = Seq("-feature", "-language:implicitConversions", "-indent", "-Xwiki-syntax", "-Xmax-inlines", "128", "-new-syntax")

// val scala2Opts = Seq("-feature", "-language:implicitConversions", "-explaintypes", "-deprecation", "-Ytasty-reader")
// val scala3Opts = Seq("-feature", "-language:implicitConversions", "-explain-types", "-indent", "-new-syntax")

lazy val root = (project in file("."))
  .settings(
    name := "kittens",
    organization := "sjb.ia.ga",
    organizationName := "sjbiaga",
    version := "1.0",
    maxErrors := 5,
    scalaVersion := "3.7.1-RC2",
    crossScalaVersions ++= Seq("2.13.16", "3.7.1-RC2"),
    scalacOptions ++= scala3Opts, // :+ "-Xprint:typer",
    libraryDependencies ++= Seq(catseffect, catscore, catsfree, parsercombinators, algebra, alleycats)
  )

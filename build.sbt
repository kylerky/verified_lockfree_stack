ThisBuild / scalaVersion := "2.13.6"
ThisBuild / organization := "ch.epfl"

lazy val root = project
  .in(file("."))
  .aggregate(core)

lazy val core = project
  .in(file("core"))
  .settings(name := "lock_free_stack")

// lazy val verified = project
//   .in(file("verified"))
//   .enablePlugins(StainlessPlugin)
//   .settings(name := "verified_lock_free_stack")

name := "perfect"

organization := "ch.epfl.lara.synthesis"

scalaVersion := "2.11.8"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"

libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.0.6"

//scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

resolvers += "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases"

resolvers += "uuverifiers" at "http://logicrunch.it.uu.se:4096/~wv/maven"

libraryDependencies += "ch.epfl.lara" %% "inox" % "1.0.2-81-g9f77744"

libraryDependencies ++= Seq("io.github.nicolasstucki" %% "multisets" % "0.4")
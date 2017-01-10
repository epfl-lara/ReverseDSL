addSbtPlugin("com.artima.supersafe" % "sbtplugin" % "1.1.0")

resolvers ++= Seq(
  Resolver.sonatypeRepo("releases"),
  Resolver.sonatypeRepo("snapshots")
)


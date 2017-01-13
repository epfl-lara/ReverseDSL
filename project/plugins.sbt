addSbtPlugin("com.artima.supersafe" % "sbtplugin" % "1.1.0")

resolvers += "Artima Maven Repository" at "http://repo.artima.com/releases"

resolvers ++= Seq(
  Resolver.sonatypeRepo("releases"),
  Resolver.sonatypeRepo("snapshots")
)


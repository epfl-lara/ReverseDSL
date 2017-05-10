package perfect
package lenses
import inox._
import inox.trees._
import inox.trees.dsl._

/**
  * Created by Mikael on 10/05/2017.
  */
object FunctionDefinitions {
  import Utils._

  // filter definition in inox
  val filterFunDef = mkFunDef(filter)("A"){ case Seq(tp) =>
    (Seq("ls" :: T(list)(tp), "f" :: FunctionType(Seq(tp), BooleanType)),
      T(list)(tp),
      { case Seq(ls, f) =>
        if_(ls.isInstOf(T(cons)(tp))) {
          let("c"::T(cons)(tp), ls.asInstOf(T(cons)(tp)))(c =>
            let("head"::tp, c.getField(head))( head =>
              if_(Application(f, Seq(head))){
                ADT(T(cons)(tp), Seq(head, E(filter)(tp)(c.getField(tail), f)))
              } else_ {
                E(filter)(tp)(c.getField(tail), f)
              }
            )
          )
        } else_ {
          ADT(T(nil)(tp), Seq())
        }
      })
  }

  // Map definition in inox
  val mapFunDef = mkFunDef(map)("A", "B"){ case Seq(tA, tB) =>
    (Seq("ls" :: T(list)(tA), "f" :: FunctionType(Seq(tA), tB)),
      T(list)(tB),
      { case Seq(ls, f) =>
        if_(ls.isInstOf(T(cons)(tA))) {
          let("c"::T(cons)(tA), ls.asInstOf(T(cons)(tA)))(c =>
            let("head"::tA, c.getField(head))( head =>
              ADT(T(cons)(tB), Seq(Application(f, Seq(head)), E(map)(tA, tB)(c.getField(tail), f)))
            )
          )
        } else_ {
          ADT(T(nil)(tB), Seq())
        }
      })
  }

  val funDefs = List[FunDef](
    filterFunDef,
    mapFunDef
  )
}

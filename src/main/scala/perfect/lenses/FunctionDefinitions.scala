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
  import StringConcatExtended._

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

  val mkStringFunDef = mkFunDef(Utils.mkString)(){ case Seq() =>
    (Seq("ls" :: T(list)(StringType), "infix"::StringType),
      StringType,
      { case Seq(ls, infix) =>
        if_(ls.isInstOf(T(cons)(StringType))) {
          let("c"::T(cons)(StringType), ls.asInstOf(T(cons)(StringType)))(c =>
            let("head"::StringType, c.getField(head))( head =>
              let("tail"::T(list)(StringType), c.getField(tail))( tail =>
                if_(tail.isInstOf(T(cons)(StringType))) {
                  head +& infix +& FunctionInvocation(Utils.mkString, Seq(), Seq(tail, infix))
                } else_ {
                  head
                }
              )
            )
          )
        } else_ {
          StringLiteral("")
        }
      })
  }

  // Rec definition in inox.
  val recFunDef = mkFunDef( rec)("A1", "A2", "B"){ case Seq(tA1, tA2, tB) =>
    (Seq("F" :: FunctionType(Seq(FunctionType(Seq(tA1, tA2), tB), tA1, tA2), tB), "x1" :: tA1, "x2" :: tA2),
      tB,
      { case Seq(f, x1, x2) =>
        f(\("a1"::tA1, "a2"::tA2)((a1, a2) => E(rec)(tA1, tA2, tB)(f, a1, a2)), x1, x2)
      })
  }

  val funDefs = List[FunDef](
    filterFunDef,
    mapFunDef,
    mkStringFunDef,
    recFunDef
  )
}

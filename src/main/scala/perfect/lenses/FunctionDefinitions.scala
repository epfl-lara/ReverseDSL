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


  // Concat definition in inox
  val listConcatFunDef = mkFunDef(Utils.listconcat)("A"){ case Seq(tA) =>
    (Seq("left" :: T(list)(tA), "right" :: T(list)(tA)),
      T(list)(tA),
      { case Seq(left, right) =>
        if_(left.isInstOf(T(cons)(tA))) {
          let("c"::T(cons)(tA), left.asInstOf(T(cons)(tA)))(c =>
            ADT(T(cons)(tA),
              Seq(c.getField(head), E(Utils.listconcat)(tA)(c.getField(tail), right)))
          )
        } else_ {
          right
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

  import ImplicitTuples._

  // Flatmap definition in inox
  val flatMapFunDef = mkFunDef(Utils.flatmap)("A", "B"){ case Seq(tA, tB) =>
    (Seq("ls" :: T(list)(tA), "f" :: FunctionType(Seq(tA), T(list)(tB))),
      T(list)(tB),
      { case Seq(ls, f) =>
        if_(ls.isInstOf(T(cons)(tA))) {
          let("c"::T(cons)(tA), ls.asInstOf(T(cons)(tA)))(c =>
            let("headMapped"::T(list)(tB), f(c.getField(head)))( headMapped =>
              E(listconcat)(tB)(headMapped, E(Utils.flatmap)(tA, tB)(c.getField(tail), f))
            )
          )
        } else_ {
          ADT(T(nil)(tB), Seq())
        }
      })
  }

  val sortWithFunDef= mkFunDef(sortWith)("A"){ case Seq(tA) =>
    (Seq("in" :: T(list)(tA), "comp" :: FunctionType(Seq(tA, tA), IntegerType)),
      T(list)(tA),
      { case Seq(input, comp) =>
        if_(input.isInstOf(T(nil)(tA)) || input.asInstOf(T(cons)(tA)).getField(tail).isInstOf(T(nil)(tA))) {
          input
        } else_ {
          let("r"::T(tuple2)(T(list)(tA), T(list)(tA)),
            FunctionInvocation(splitEven, Seq(tA), Seq(input)))( r=>
            FunctionInvocation(merge, Seq(tA), Seq(
              FunctionInvocation(sortWith, Seq(tA), Seq(r.getField(_1), comp)),
              FunctionInvocation(sortWith, Seq(tA), Seq(r.getField(_2), comp)),
              comp))
          )
        }
      })
  }

  val mergeFunDef : FunDef = mkFunDef(merge)("A") { case Seq(tA) =>
    (Seq("left":: T(list)(tA), "right":: T(list)(tA), "comp" :: FunctionType(Seq(tA, tA), IntegerType)),
      T(list)(tA),
      { case Seq(left, right, comp) =>
        if_(left.isInstOf(T(cons)(tA))) {
          if_(right.isInstOf(T(cons)(tA))) {
            let("leftcons"::T(cons)(tA), left.asInstOf(T(cons)(tA)))( leftcons =>
              let("rightcons"::T(cons)(tA), right.asInstOf(T(cons)(tA)))( rightcons =>
                if_(Application(comp, Seq(leftcons.getField(head), rightcons.getField(head))) <= IntegerLiteral(BigInt(0))) {
                  ADT(T(cons)(tA), Seq(leftcons.getField(head), FunctionInvocation(merge, Seq(tA), Seq(leftcons.getField(tail), right, comp))))
                } else_ {
                  ADT(T(cons)(tA), Seq(rightcons.getField(head), FunctionInvocation(merge, Seq(tA), Seq(left, rightcons.getField(tail), comp))))
                }
              )
            )
          } else_ {
            left
          }
        } else_ {
          right
        }
      })
  }
  import ImplicitTuples.tuple2
  val splitEvenFunDef: FunDef = mkFunDef(splitEven)("A") { case Seq(tA) =>
    (Seq("l"::T(list)(tA)),
      T(tuple2)(T(list)(tA), T(list)(tA)),
      { case Seq(l) =>
        if_(l.isInstOf(T(cons)(tA))) {
          let("r"::T(tuple2)(T(list)(tA), T(list)(tA)),
            FunctionInvocation(splitEven, Seq(tA), Seq(l.asInstOf(T(cons)(tA)).getField(tail))))(r =>
            ADT(T(tuple2)(T(list)(tA), T(list)(tA)), Seq(
              ADT(T(cons)(tA), Seq(l.asInstOf(T(cons)(tA)).getField(head), r.getField(_2))),
              r.getField(_1))))
        } else_ {
          ADT(T(tuple2)(T(list)(tA), T(list)(tA)), Seq(ADT(T(nil)(tA), Seq()), ADT(T(nil)(tA), Seq())))
        }
      }
    )
  }

  val funDefs = List[FunDef](
    filterFunDef,
    mapFunDef,
    mkStringFunDef,
    recFunDef,
    listConcatFunDef,
    flatMapFunDef,
    sortWithFunDef,
    mergeFunDef,
    splitEvenFunDef
  )
}

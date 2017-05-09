package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait AssociativeLenses { self: ProgramUpdater with ContExps with Lenses =>

  /** mix-in this trait if your function is associative and keeps the values and order (e.g. String or List concat) */
  trait AssociativeConcat[A, C] { self: SemanticLens =>
    /** The greatest number it returns, the greatest difference there is between the end of the first argument and the start of second.*/
    def typeJump(a: A, b: A): Int

    def endsWith(a: A, b: A): Boolean
    def startsWith(a: A, b: A): Boolean
    def length(a: A): Int
    def take(a: A, i: Int): A
    def drop(a: A, i: Int): A
    def empty: A

    import Utils._

    def associativeInsert(leftValue_s: A, rightValue_s: A, leftAfter: A, inserted: A, rightAfter: A,
                          direction: AssociativeInsert.InsertDirection,
                          makeExpr: A => Exp,
                          subproblem: (A, A, A) => ContExp
                         ): Stream[(Seq[ContExp], Cont)] = {
      val res: List[((Seq[ContExp], Cont), (Int, Int))] = endsWith(rightValue_s, rightAfter).flatMap{ // the insertion may have happened on the right.
        //  [  leftValue    ...     ][rightValue_s  ]
        //  [ leftAfter ....            ][rightAfter]

        // rightValue => (leftAfter \ leftValue) + inserted + rightAfter
        val somethingLeft = length(leftValue_s) < length(leftAfter)
        val newLeftAfter = if(somethingLeft) drop(leftAfter, length(leftValue_s)) else empty
        val newRightAfter = rightAfter

        val newInsert = subproblem(newLeftAfter, inserted, newRightAfter)

        val newLeftValue = if(somethingLeft) { // Nothing deleted.
          makeExpr(leftValue_s)
        } else {
          makeExpr(take(leftValue_s, length(leftAfter)))
        }
        val directionWeight = direction match {
          case AssociativeInsert.InsertToRight => 0 // Best weight.
          case AssociativeInsert.InsertToLeft => 1 // Worst weight
          case AssociativeInsert.InsertAutomatic => typeJump(newLeftAfter, inserted) + typeJump(inserted, newRightAfter)
        }
        val overwriteWeight = length(rightAfter) - length(rightValue_s)

        List((((Seq(ContExp(newLeftValue), newInsert)), Cont()), (directionWeight, overwriteWeight))) // /: Log.Right_insert
      } ++
        startsWith(leftValue_s, leftAfter).flatMap{ // the insertion happened on the left.
          //  [  leftValue    ...     ][rightValue_s  ]
          //  [ leftAfter ...   ][        rightAfter  ]

          // leftValue => leftAfter + inserted + (rightAfter \ rightValue)

          val newLeftAfter = leftAfter
          val somethingRight = length(rightValue_s) < length(rightAfter)
          val newRightAfter = if(somethingRight) take(rightAfter, length(rightAfter) - length(rightValue_s)) else empty

          val newInsert = subproblem(newLeftAfter, inserted, newRightAfter)

          val newRightValue = if(somethingRight) {
            makeExpr(rightValue_s)
          } else {
            makeExpr(drop(rightValue_s, length(rightValue_s) - length(rightAfter)))
          }
          val spaceWeight = typeJump(newLeftAfter, inserted) + typeJump(inserted, newRightAfter)
          val directionWeight = direction match {
            case AssociativeInsert.InsertToRight => 1 // Worst weight
            case AssociativeInsert.InsertToLeft => 0 // Best weight
            case AssociativeInsert.InsertAutomatic => typeJump(newLeftAfter, inserted) + typeJump(inserted, newRightAfter)
          }

          val overwriteWeight = length(leftAfter) - length(leftValue_s)

          List(((Seq(newInsert, ContExp(newRightValue)), Cont()), (directionWeight, overwriteWeight))) // /: Log.Left_insert
        }

      res.sortWith{ (x, y) =>
        if(y._2._2 < 0 && x._2._2 == 0) { // If replaced parts on the right
          false
        } else if(x._2._2 < 0 && y._2._2 == 0) { // If replaced parts on the left
          true
        } else {
          // No replaced parts, or both replaced.
          // It's a simple insertion. First, try to attach to where the characters are more alike.
          // Second, if equality, attach where the most characters have been removed.
          x._2._1 < y._2._1 || (x._2._1 == y._2._1 && x._2._2 < y._2._2)
        }}.map(_._1).toStream
    }
  }

}

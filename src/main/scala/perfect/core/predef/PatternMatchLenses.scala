package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */

trait PatternMatchLenses extends PatternMatchLensesLike with ContExps with StringConcatLenses {
  self: ProgramUpdater
    with Lenses with StringLenses with ADTLenses =>

  override def buildContExpCommands = super.buildContExpCommands += PatternMatchLensGoal
  override def buildMergeCommands = super.buildMergeCommands += PatternMatchLensGoal
  /** Pattern match the input program, inserting the variables if forClone is activated.
    * The pattern with the vars replaced by their inputs must always be the original program value.
    **/
  def extractPatternMatchGoal(e: Exp): Option[(Exp, List[(Var, Exp)], Boolean)]
  def buildPatternMatchGoal(pattern: Exp, vars: List[(Var, Exp)], forClone: Boolean): Exp

  object PatternMatchLensGoal extends PatternMatchLensGoalExtractor with ContExpCommand with MergeCommand {
    def unapply(e: Exp): Option[(Exp, List[(Var, Exp)], Boolean)] = extractPatternMatchGoal(e: Exp)
    def apply(pattern: Exp, vars: List[(Var, Exp)], forClone: Boolean): Exp = buildPatternMatchGoal(pattern, vars, forClone)

    object Eval extends EvalContExpCommand {
      def unapply(e: Exp): Option[Exp] = e match {
        case PatternMatchLensGoal(before, variables, forClone) =>
          Some(replaceFromVars(variables.toMap, before))
        case _ => None
      }
    }
    def merge(e1: Exp, e2: Exp)(implicit symbols: Symbols): Option[(Exp, Seq[(Var, KnownValue)])] = {
      e2 match {
        case PatternMatchLensGoal(before, variables, forClone) =>
          e1 match {
            case CloneTextMultiple.Goal(left2, textVarRight2) =>
              e2 match {
                case CloneTextMultiple.Goal(left1, textVarRight1) =>
                  CloneTextMultiple.Goal.merge(left1, textVarRight1, left2, textVarRight2)
                case _ => None
              }

            case PatternMatchLensGoal(before2, variables2, forClone2) =>
              None
            //            PatternMatch.Goal.merge(before, variables, forClone, before2, variables2, forClone2)
            case _ => None
          }
        case _ => None
      }
    }
  }

  /** Inserts a variable for a given selected text. Simpler than CloneTextMultiple. */
  object CloneText  {
    def apply(left: String, text: String, right: String)(implicit symbols: Symbols): ContExp = {
      val variable = StringLiteral.mkVar(text)
      apply(left, text, right, variable)
    }
    def apply(left: String, text: String, right: String, insertedVar: Var)(implicit symbols: Symbols): ContExp = {
      CloneTextMultiple(left, List((text, insertedVar, right)))
    }
  }

  object CloneTextMultiple extends StringConcatHelpers {
    def StringConcat = self.StringConcat
    def apply(left: String, textVarRights: List[(String, Var, String)])(implicit symbols: Symbols): ContExp =
      ContExp(Goal(left, textVarRights))

    object Goal {
      def apply(left: String, textVarRights: List[(String, Var, String)])(implicit symbols: Symbols) = {
        val before = ((StringLiteral(left): Exp) /: textVarRights) {
          case (e, (middle, v, right)) => e +<>& v +<>& StringLiteral(right)
        }
        PatternMatchLensGoal(before, textVarRights.map(x => x._2 -> StringLiteral(x._1)), true)
      }
      def unapply(e: Exp)(implicit symbols: Symbols): Option[(String, List[(String, Var, String)])] = e match {
        case PatternMatchLensGoal(StringConcat.Exhaustive(strs), variables, true) =>
          def getVarValue(v: Var): String = variables.collectFirst {
            case (v2, StringLiteral(s)) if v2 == v => s
          }.get

          def unbuild(e: List[Exp]): Option[(String, List[(String, Var, String)])] = e match {
            case Nil => Some(("", Nil))
            case StringLiteral(text) :: tail => unbuild(tail).map{ case (left, l) =>
              ((text+left), l)
            }
            case Var(v)::tail => unbuild(tail).map{ case (left, l) =>
              ("", (getVarValue(v), v, left)::l)
            }
            case _ => None
          }
          unbuild(strs)
        case _ => None
      }

      private def SplitVar(v1: Var, inserted: Set[Var]): (Var, Var) = {
        val v1p1 = StringLiteral.mkVar(v1, (inserted + v1).toSeq :_*)
        val v1p2 = StringLiteral.mkVar(v1, (inserted + v1 + v1p1).toSeq :_*)
        (v1p1, v1p2)
      }
      def merge(left1: String, textVarRight1: List[(String, Var, String)],
                left2: String, textVarRight2: List[(String, Var, String)], inserted: Set[Var] = Set())(implicit symbols: Symbols): Option[(Exp, Seq[(Var, KnownValue)])] = {
        if(left1.length > 0 && left2.length > 0) {
          if(left1.length <= left2.length) {
            assert(left2.startsWith(left1))
            merge("", textVarRight1,
              left2.substring(0, left1.length), textVarRight2, inserted).map{
              case (Goal(newLeft1, newTextVarRight1), vk) =>
                (Goal(left1 + newLeft1, newTextVarRight1), vk)
            }
          } else { // if(left1.length > left2.length)
            merge(left2, textVarRight2, left1, textVarRight1, inserted)
          }
        } else {
          // At least one of left1 and left2 is empty.
          (textVarRight1, textVarRight2) match {
            case (Nil, Nil) if left1 == left2 =>
              Some((apply(left1, Nil), Nil))
            case (Nil, textVarRight2) if left1.startsWith(left2) =>
              Some((apply(left2, textVarRight2), Nil))
            case (textVarRight1, Nil) if left2.startsWith(left1) =>
              Some((apply(left1, textVarRight1), Nil))
            case ((middle1, v1, right1) :: tail1, (middle2, v2, right2) :: tail2) =>
              if (left1.length == 0) {
                if (left2.startsWith(middle1)) {
                  // We can insert the first variable in place of left2.
                  val updatedLeft2 = left2.substring(middle1.length)
                  val updatedRight1 = right1
                  merge(updatedRight1, tail1, updatedLeft2, textVarRight2, inserted).map {
                    case (Goal(leftNew, textVarRightNew), mp) =>
                      (Goal(left1, (middle1, v1, leftNew) :: textVarRightNew), mp)
                  }
                } else if(left2.length == 0) { // Overlapping between variables
                  if(middle1.length == middle2.length) {
                    if(inserted(v1)) {
                      if(inserted(v2)) {
                        //Log("[internal warning] tried to merge two inserted variables, makes no sense.")
                        None
                      } else {
                        merge(right1, tail1, right2, tail2, inserted) map {
                          case (Goal(leftNew, textVarRightNew), mp) =>
                            (Goal("", (middle1, v1, leftNew)::textVarRightNew),
                              (v2 -> InsertVariable(v1)) +: mp)
                        }
                      }
                    } else {
                      if(inserted(v2)) {
                        merge(left2, textVarRight2, left1, textVarRight1, inserted)
                      } else { // We insert a new variable and link the two other variables.
                        val v = StringLiteral.mkVar(v1, v2)
                        merge(right1, tail1, right2, tail2, inserted) map {
                          case (Goal(leftNew, textVarRightNew), mp) =>
                            (Goal("", (middle1, v, leftNew)::textVarRightNew),
                              (v1 -> InsertVariable(v)) +: (v2 -> InsertVariable(v)) +: mp)
                        }
                      }
                    }
                  } else if(middle1.length < middle2.length) {
                    if(inserted(v1)) {
                      if(inserted(v2)) {
                        //Log("[internal warning] tried to merge two inserted variables, makes no sense.")
                        None
                      } else {
                        // We split v2 into a second variable.
                        val (_, v2p2) = SplitVar(v2, inserted)
                        val news = v2 -> InsertVariable(v1 +& v2p2)
                        val positionSplit = middle1.length
                        val newMiddle2 = middle2.substring(positionSplit)
                        merge(right1, tail1, "", (newMiddle2, v2p2, right2)::tail2, inserted) map {
                          case (Goal(leftNew, textVarRightNew), mp) =>
                            (Goal("", (middle1, v1, leftNew)::textVarRightNew), news +: mp)
                        }
                      }
                    } else {
                      val (v2p1, v2p2) = SplitVar(v2, inserted)
                      val news = v2 -> InsertVariable(v2p1 +& v2p2)
                      val position = middle1.length
                      val middle21 = middle2.substring(0, position)
                      val middle22 = middle2.substring(position)
                      merge(left1, textVarRight1,
                        left2, (middle21, v2p1, "") :: (middle22, v2p2, right2) :: tail2, inserted ++ Seq(v2p1, v2p2)
                      ) map {
                        case (ctm, mp) => (ctm, news +: mp)
                      }
                    }
                  } else {
                    merge(left2, textVarRight2, left1, textVarRight1, inserted)
                  }
                } else { // Partial overlapping of a variable on the left string of the next.
                  assert(middle1.startsWith(left2)) // We need to introduce one variable for the overlap.
                  val (v1p1, v1p2) = SplitVar(v1, inserted)
                  val news = v1 -> InsertVariable(v1p1 +& v1p2)
                  val positionSplit = left2.length
                  val newMiddle1 = middle1.substring(0, positionSplit) // should equal left2.
                  val newLeft1 = middle1.substring(positionSplit)

                  merge(left1, (newMiddle1, v1p1, "") :: (newLeft1, v1p2, right1) :: tail1,
                    left2, textVarRight2, inserted ++ Seq(v1p1, v1p2)
                  ).map {
                    case (ctm, mp) =>
                      (ctm, news +: mp)
                  }
                }
              } else { //if (left2.length == 0)
                merge(left2, textVarRight2, left1, textVarRight1, inserted)
              }
          }
        }
      }
    }
  }

  object PatternMatchLens extends PatternMatchLensLike(StringLiteral, StringConcat, ADT, PatternMatchLensGoal)
}


package perfect
package semanticlenses

import inox.trees._
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 09/05/2017.
  */
trait FunctionInvocationExtractor extends MultipleArgExtractor {
  def identifier: inox.Identifier

  def put(tpes: Seq[Type])(originalArgsValues: Seq[ProgramFormula], out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[(Seq[ProgramFormula], Formula)]

  def extract(e: Expr)(implicit symbols: Symbols, cache: Cache): Option[
    ( Seq[Expr],
      (Seq[ProgramFormula], ProgramFormula) => Stream[(Seq[ProgramFormula], Formula)],
      Seq[Expr] => Expr
      )] = e match {
    case FunctionInvocation(id, tpes, args) if id == identifier =>
      Some((args,
        (originalArgsValues: Seq[ProgramFormula], out: ProgramFormula) => put(tpes)(originalArgsValues, out),
        (newArgs: Seq[Expr]) => FunctionInvocation(identifier, tpes, newArgs)
      ))
    case _ => None
  }
}
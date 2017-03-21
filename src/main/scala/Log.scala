/**
  * Created by Mikael on 15/03/2017.
  */

import scala.language.dynamics
object Log extends LogLike with Dynamic {
  var activate = true
  def prefix(p: String): LogLike = new LogLike {
    override def apply(s: Any) = if(activate) {
      super.apply(p+s)
    }
  }
  def selectDynamic(name: String) = prefix(name.replaceAll("_", " ") + ": ")
}

trait LogLike {
  import Log._
  def apply(s: Any) = if(activate) println(s.toString.replaceAll("""\$""", "").replaceAll("""ValDef\((\w+), ?\S+, ?Set\(\)\)""", "$1"))
  def =:[A](s: A): A = {
    apply(s)
    s
  }
  def /:[A](s: A): A = this.=:(s)
  def /::[A](s: Stream[A]): Stream[A] = {
    s.zipWithIndex.map{ case(x, i) =>
      this.apply(s"Partial solution #${i+1}\n"+x)
      x
    }
  }
  def :=[A](s: A): A = {
    apply(s)
    s
  }
}

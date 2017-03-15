/**
  * Created by Mikael on 15/03/2017.
  */

import scala.language.dynamics
object Log extends LogLike with Dynamic {
  var activate = false
  def prefix(p: String): LogLike = new LogLike {
    override def apply(s: Any) = if(activate) {
      print(p)
      super.apply(s)
    }
  }
  def selectDynamic(name: String) = prefix(name.replaceAll("_", " ") + ": ")
}

trait LogLike {
  import Log._
  def apply(s: Any) = if(activate) println(s)
  def =:[A](s: A): A = {
    apply(s)
    s
  }
  def /:[A](s: A): A = this.=:(s)
  def /::[A](s: Stream[A]): Stream[A] = {
    s.map{ x =>
      this.apply(x)
      x
    }
  }
  def :=[A](s: A): A = {
    apply(s)
    s
  }
}

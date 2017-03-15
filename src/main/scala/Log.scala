/**
  * Created by Mikael on 15/03/2017.
  */
object Log {
  var activate = false
  def apply(s: Any) = if(activate) println(s)
}

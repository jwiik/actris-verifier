package fi.abo.it.actortool.util

object Analysis {
  def allEqual[T](list: List[T]) = {
    list.tails.flatMap {
      case x :: rest => rest.map { y => x == y }
      case _ => List()
    }.forall(x => x)
  }
}
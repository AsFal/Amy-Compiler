object matchError{
  def isDefined(o: O.Option): Boolean = {
    o match {
      case L.Nil() => false
      case _ => true
    }
  }
}
object Ambiguous {
  implicit def bool2int(b: Boolean): Int = {
      if (b) { 3 }
      else { -1 }
  }
  implicit def int2bool(i: Int): Boolean = {i == 3}
  4 == true // Ambiguous conversion error
}
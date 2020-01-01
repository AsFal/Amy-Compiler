object BadForm {
  implicit def invert(b: Boolean): Boolean = {!b}
  implicit def bool2int(b: Boolean, n: Int): Int = {
      if (b) {n} else {-1}
  } // Bad conversion error
}
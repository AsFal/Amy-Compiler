object Ambiguous {
  implicit def bool2int(b: Boolean): Int = {
      if (b) { 3 }
      else { -1 }
  }
  implicit def bool2int2(b: Boolean): Int = {
      if (b) { 4 }
      else { -9 }
  }
  2 || false  // Ambiguous conversion error
}
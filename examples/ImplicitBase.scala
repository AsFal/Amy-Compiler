object BaseCase {
  implicit def int2bool(i: Int): Boolean = {i == 1}

  val b: Boolean = 3;
  2 || false;
  2 || b;
  false == 2;
  if (true) {
      false
  } else {
      2
  }
}
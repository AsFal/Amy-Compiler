object BaseCase {
  implicit def int2bool(i: Int): Boolean = {i == 1}

  val b: Int = true;
  2 || false;
  2 || b;
  2 == false;
  if (true) {
      2
  } else {
      true
  }
}
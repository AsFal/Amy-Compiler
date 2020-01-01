object Transitive {
  implicit def int2Bool(i: Int): Boolean = {i == 0}
  implicit def bool2Str(b: Boolean): String = {if (b) {"true"} else {"false"}}
  "Hello World" ++ 3 // Type error
}
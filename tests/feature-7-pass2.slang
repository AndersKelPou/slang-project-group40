method factorial(x: Int): Int
    requires 0 <= x
    ensures true
    decreases x
{
  match {
    x == 0 =>
        return 1,
    x > 0 =>
        var res: Int;
        res := factorial(x - 1);
        return x * res
  }
}
method sqrt(x: Int): Int
    requires 0 <= x
    ensures true
    decreases x
{
  match {
    x == 4 =>
        return 2,
    true =>
        var res: Int;
        // @CheckError
        res := sqrt(x);
        return res
  }
}
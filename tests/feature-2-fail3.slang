method inc(n: Int): Int
    requires n >= 0
    ensures result == n + 1
{
    return n + 1
}

method test()
{
    var x := 4;
    x := inc(x);
    // @CheckError
    assert false
}
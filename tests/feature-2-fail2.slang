method add1(n: Int): Int
    requires n >= 0
    ensures 1 <= result && n < result // && result == n + 1
{
    return n + 1
}

method test(): Int
    ensures result > 4
{
    var res := 0;
    res := add1(4);
    // @CheckError
    assert res == 5;
    return res
}
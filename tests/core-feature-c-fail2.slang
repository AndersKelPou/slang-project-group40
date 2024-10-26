method return_too_fast(x: Int): Int 
    requires x == 0
    ensures result < x - 5
{
    var y: Int := 4;
    y := y + 9;
    // @CheckError
    return y;
    x := 2;
    return y
}
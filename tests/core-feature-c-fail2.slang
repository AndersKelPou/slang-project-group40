method return_too_fast(x: Int): Int 
    requires x == 0
    // @CheckError
    ensures result < x - 5
{
    var y: Int := 4;
    y := y + 9;
    // CheckError here no longer is true, since early return is imlpemented
    return y;
    x := 2;
    return y
}
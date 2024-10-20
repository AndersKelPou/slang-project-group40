method return_too_fast(x: Int): Int 
    requires x >= 4
    ensures result >= x
{

    var acc: Int;
    acc := x / 2;
    // @CheckError
    return acc;
    acc := acc * 6;
    return acc
}
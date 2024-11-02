method client(n: Int): Int
    ensures acc == n * (n + 1) / 2
{
    var acc: Int := 0;
    for i in 1..(n + 1)
       // invariant ...
    {
        acc := acc + i
    };
    return acc
}
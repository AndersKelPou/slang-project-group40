method doubleLoop(n: Int, m:Int): Int
    requires n >= 0
    requires m >= 0
    ensures result == n * m
{
    var i: Int := 0;
    var j: Int := 0;
    var r: Int := 0;

    loop
    invariant i >= 0
    invariant i <= n
    invariant r == m * i
    {
        i < n => i := i + 1;
                j := 0;
                loop
                invariant j >= 0
                invariant j <= m
                invariant r == (i - 1) * m + j
                {
                    j < m => 
                            j := j + 1;
                            r := r + 1
                };
                assert j == m
    };
    return r
}
method cube(n : Int) : Int
    requires n >= 0
    ensures result == n*n*n
{
    var r : Int := 0;
    var s : Int := 0;
    var i : Int := 0;
    var t : Int := 0;
    loop// @CheckError
        invariant 0 <= i && i <= n
        invariant r == i * i * i
        invariant s == 3 * i * i
        invariant t == 3 * i
    {
        i != n => 
            r := r + s + t + 1;
            s := s + t + t + 1; // should be + 3
            t := t + 3;
            i := i + 1
    };
    assert r == n*n*n;
    return r
}
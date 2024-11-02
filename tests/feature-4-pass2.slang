method findDifferenceIterative(n: Int, m: Int) 
    requires m >= n
{
    var res: Int := 0;
    for i in n..m {
        res := res + 1
    };
    assert res == m - n
}
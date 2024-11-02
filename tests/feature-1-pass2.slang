method addFiveIteratively(n : Int) 
{
    var originalN : Int := n;
    for i in 5..10 {
        n := n + 1
    };
    assert n == originalN + 5
}
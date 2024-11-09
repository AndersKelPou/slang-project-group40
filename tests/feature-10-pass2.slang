method calc(n: Int)
    requires n >= 0
{
    match {
        n == 0 => 
            return,
        n > 0 => 
            var m: Int := n * n + 3;
            return
    };
    assert false
}
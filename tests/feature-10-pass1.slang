method sumn(n: Int): Int
    requires n >= 0
    ensures result == 0
    decreases n
{
    match {
        n == 0 => 
            return 0,
        true => 
            var res: Int;
            //Altered since recursive method calls are not implemented at the time of testing
            res := 0;
            return res
    };
    assert false // not reachable, passes
}
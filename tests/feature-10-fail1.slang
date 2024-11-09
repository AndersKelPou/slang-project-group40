method sumn(n: Int): Int
    requires n >= 0
    ensures result == 0
    decreases n
{
    match {
        n == 0 => 
            //Altered to not return anything in this branch
            assert true,
        true => 
            var res: Int;
            res := 0;
            return res
    };
    // @CheckError
    assert false;
    return 0
}
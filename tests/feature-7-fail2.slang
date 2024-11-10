method sumn(x:Int, n: Int): Int
    requires n >= 0
    decreases n
{
    var ret: Int;
    match {
        n == 0 => 
            ret := 0,
        n > 0 => 
            var res: Int;
            // @CheckError
            res := sumn(x - 1, n);
            ret := res + n
    };
    return ret
}
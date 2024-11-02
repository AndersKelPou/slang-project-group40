method wrongRange() 
{
    var res : Int := 0;
    // @CheckError
    for i in 5..3 {
        res := res + i
    };
    assert res >= 0
}
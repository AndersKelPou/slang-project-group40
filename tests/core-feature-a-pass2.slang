method m(x: Int) : Int
requires x >= 0
ensures result > 0
{
    var y: Int := x - 5;
    match {
        x == 0 =>
            match {
                true => y := 5
            },
        x > 0 =>
            match {
                y < 0 => y := 10,
                y >= 0 => y := 18
            }
    };
    assert y == 5 || y == 10 || y == 18;
    return y
}
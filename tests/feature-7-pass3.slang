method B(x: Int, y: Int): Int
    requires 0 <= x
    requires 0 <= y
    decreases 4 * x + y
{
    var z: Int;
    match {
        x == 0 => z := 0,
        x != 0 && y == 0 => z := B(x - 1, 3),
        x != 0 && y != 0 => z := B(x, y - 1)
    };
    return z
}
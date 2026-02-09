int mod (int x, int y)
/*@ requires y != 0i32;
    ensures return == x % y; @*/
{
    return x % y;
}

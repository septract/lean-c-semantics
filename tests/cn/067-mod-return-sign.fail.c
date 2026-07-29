int different_sign (int x, unsigned int y)
/*@ requires y != 0u32;
    ensures return == x % y; @*/
{
    return x % y;
}

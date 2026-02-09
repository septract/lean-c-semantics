unsigned int to_unsigned(int x)
/*@ requires x >= 0i32;
    ensures return == (u32)x; @*/
{
    return (unsigned int)x;
}

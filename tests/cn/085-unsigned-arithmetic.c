unsigned int add_unsigned(unsigned int x, unsigned int y)
/*@ requires x <= 1000u32;
    requires y <= 1000u32;
    ensures return == x + y; @*/
{
    return x + y;
}

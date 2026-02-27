unsigned int mod (unsigned int x, int y)
/*@ requires y > 0i32;
     ensures return == x % (u32)y; @*/
{
    return x % y;
}

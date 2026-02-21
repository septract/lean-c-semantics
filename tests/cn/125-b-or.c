// Ported from CN test suite: b_or.c
int f(int x, int y)
    /*@ ensures return == x | y; @*/
{
    return x | y;
}

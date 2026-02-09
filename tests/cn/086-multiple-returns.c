int max(int x, int y)
/*@ ensures (x >= y) ? (return == x) : (return == y); @*/
{
    if (x >= y) return x;
    else return y;
}

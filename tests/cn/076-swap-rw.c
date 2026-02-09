// From cn-tutorial: swap using RW resources
void swap_1(int *a, int *b)
/*@ requires
    take Pa = RW(a);
    take Pb = RW(b);
    ensures
    take Qa = RW(a);
    take Qb = RW(b);
    Qb == Pa;
    Qa == Pb; @*/
{
  int temp = *a;
  *a = *b;
  *b = temp;
}

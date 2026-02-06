// CN test: Negation with INT_MIN overflow guard
// From cn-tutorial: neg_1.c
// Tests: CN built-in function MINi32(), negation in spec
// NEEDS: MINi32() builtin handling

int negate(int i)
/*@ requires -i > MINi32(); @*/
{
  return -i;
}

int main(void)
{
  return negate(-42);
}

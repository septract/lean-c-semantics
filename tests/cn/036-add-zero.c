// CN test: Addition with both args constrained to zero
// From cn-tutorial: add_1.c
// Tests: basic requires/ensures with return and arithmetic

signed int add_zero(signed int x, signed int y)
/*@ requires x == 0; y == 0;
    ensures return == x + y; @*/
{
  signed int i;
  i = x + y;
  return i;
}

int main(void)
{
  return add_zero(0, 0);
}

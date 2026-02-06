// CN test: Addition with one arg constrained to zero
// From cn-tutorial: add_2.c
// Tests: constraint with one free parameter, return value tracking

signed int add_one_zero(signed int x, signed int y)
/*@ requires x == 0;
    ensures return == y; @*/
{
  signed int i;
  i = x + y;
  return i;
}

int main(void)
{
  return add_one_zero(0, 42);
}

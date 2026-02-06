// CN test: Decrement and return
// Tests: subtraction in return value, simple overflow guard

int decrement(int x)
/*@ requires x > 0;
    ensures return == x - 1; @*/
{
  return x - 1;
}

int main(void)
{
  return decrement(43);
}

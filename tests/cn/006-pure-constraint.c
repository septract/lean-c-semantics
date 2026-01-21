// CN test: Pure constraint only (no memory operations)
// This tests constraint handling without memory/resource issues
int positive(int x)
/*@ requires x > 0;
    ensures return == x; @*/
{
  return x;
}

int main(void)
{
  return positive(42);
}

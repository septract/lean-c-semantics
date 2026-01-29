// Read in unseq, write after - should NOT race (properly sequenced)
// EXPECTED: return 0 (no UB)
int x;

int main(void)
{
  int tmp;
  // Read x in an expression, then write after
  tmp = x + 0;  // Just read
  x = 1;        // Write after - properly sequenced
  return 0;
}

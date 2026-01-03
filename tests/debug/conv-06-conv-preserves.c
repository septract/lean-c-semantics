// Test: Converting ULONG_MAX to unsigned long should preserve it
int main(void) {
  unsigned long x = 18446744073709551615UL;
  unsigned long y = (unsigned long)x;
  return x == y ? 1 : 0;
}

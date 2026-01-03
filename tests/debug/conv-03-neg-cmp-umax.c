// Test: -1 < ULONG_MAX as unsigned should be 0 (both are ULONG_MAX)
int main(void) {
  int a = -1;
  unsigned long b = 18446744073709551615UL;
  // When comparing int with unsigned long, int is converted to unsigned long
  // -1 as unsigned long = ULONG_MAX
  // So ULONG_MAX < ULONG_MAX = false = 0
  return a < b;
}

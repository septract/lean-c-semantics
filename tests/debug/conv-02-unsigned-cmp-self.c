// Test: ULONG_MAX < ULONG_MAX should be 0 (false)
int main(void) {
  unsigned long x = 18446744073709551615UL;
  unsigned long y = 18446744073709551615UL;
  return x < y;
}

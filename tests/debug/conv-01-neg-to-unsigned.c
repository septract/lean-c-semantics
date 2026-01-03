// Test: -1 converted to unsigned long should be ULONG_MAX
int main(void) {
  unsigned long x = -1;
  return x == 18446744073709551615UL ? 1 : 0;
}

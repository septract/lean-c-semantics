// Test: Explicit conversion to variables first
int main(void) {
  int a = -1;
  unsigned long b = 18446744073709551615UL;
  unsigned long conv_a = (unsigned long)a;  // Should be ULONG_MAX
  unsigned long conv_b = b;                  // Already ULONG_MAX
  // Now compare: ULONG_MAX < ULONG_MAX = false = 0
  return conv_a < conv_b;
}

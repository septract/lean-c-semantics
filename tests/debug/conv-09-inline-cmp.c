// Test: Inline cast in comparison (no intermediate variable)
int main(void) {
  int a = -1;
  unsigned long b = 18446744073709551615UL;
  // Inline cast: (unsigned long)a < b
  return (unsigned long)a < b;
}

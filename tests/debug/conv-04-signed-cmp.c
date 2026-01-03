// Test: -1 < large signed long should be 1 (true)
int main(void) {
  int a = -1;
  long b = 9223372036854775807L;  // LONG_MAX
  // Both are signed, so -1 < LONG_MAX = true = 1
  return a < b;
}

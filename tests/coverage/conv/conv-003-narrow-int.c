// Test: int to char truncation
// Exercises: PEconv_int narrowing conversion
int main(void) {
  int x = 300;
  char c = x;
  // 300 mod 256 = 44; if char is signed, 300 - 256 = 44
  // Result is implementation-defined for signed char
  (void)c;
  return 0;
}

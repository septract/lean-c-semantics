// Test: unsigned integer wrapping (C11 6.3.1.3)
// Conversion of out-of-range values to unsigned types wraps modularly
// Audit: M9 - wrapping formula verification
int main(void) {
  // -1 converted to unsigned char: 256 + (-1) = 255
  unsigned char uc = (unsigned char)-1;

  // Large positive to unsigned char: 300 % 256 = 44
  unsigned char uc2 = (unsigned char)300;

  // 255 + 44 = 299, take low byte to fit return
  // Actually return as int to avoid wrap: 255 + 44 = 299
  // But main returns int, so this is fine
  return (int)uc + (int)uc2;  // 255 + 44 = 299, but exit truncates to 299 % 256 = 43
}

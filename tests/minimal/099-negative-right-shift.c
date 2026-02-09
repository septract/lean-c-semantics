// Test: right shift of negative numbers
// C11 6.5.7: implementation-defined for signed types
// Cerberus uses truncated division: -7 / 2 = -3
// Audit: M10 - shift operations may differ for negative numbers
int main(void) {
  int x = -8;
  int r1 = x >> 1;  // implementation-defined: should be -4 (arithmetic shift)
  int r2 = x >> 2;  // implementation-defined: should be -2

  // -4 + (-2) = -6, negate to get positive return
  return -(r1 + r2);
}

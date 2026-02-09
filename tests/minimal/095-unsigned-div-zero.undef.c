// Test: unsigned division by zero is UB (C11 6.5.5)
// Exercises wrapIntOp path (unsigned uses wrapping, not exceptional condition)
// Audit: C3 - wrapIntOp returned 0 instead of UB
int main(void) {
  unsigned int x = 10;
  unsigned int y = 0;
  return x / y;  // UB: division by zero (even for unsigned)
}

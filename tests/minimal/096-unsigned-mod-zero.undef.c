// Test: unsigned modulo by zero is UB (C11 6.5.5)
// Exercises wrapIntOp path for remainder
// Audit: C3 - wrapIntOp returned 0 instead of UB
int main(void) {
  unsigned int x = 10;
  unsigned int y = 0;
  return x % y;  // UB: modulo by zero
}

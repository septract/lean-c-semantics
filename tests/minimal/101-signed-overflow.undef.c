// Test: signed integer overflow is UB (C11 6.5)
// Exercises catchExceptionalOp path
// Audit: C3 - ensures overflow detection works correctly
#include <limits.h>
int main(void) {
  int x = INT_MAX;
  int y = x + 1;  // UB: signed overflow
  return y;
}

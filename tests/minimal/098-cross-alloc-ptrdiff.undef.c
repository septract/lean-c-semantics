// Test: pointer subtraction across different allocations is UB (C11 6.5.6)
// Audit: M5 - diffPtrval returns 0 instead of error
#include <stddef.h>
int main(void) {
  int a = 1;
  int b = 2;
  ptrdiff_t d = &a - &b;  // UB: pointers to different objects
  return (int)d;
}

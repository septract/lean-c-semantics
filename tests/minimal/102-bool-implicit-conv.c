// Test: implicit _Bool conversion in expressions
// When assigning to _Bool, the value is compared against 0
// Audit: C1 - _Bool conversion in various contexts
#include <stdbool.h>
int main(void) {
  int large = 1000;
  _Bool b = large;  // implicit conversion: 1000 != 0, so b = 1

  int neg = -42;
  _Bool b2 = neg;   // implicit conversion: -42 != 0, so b2 = 1

  // Test with pointer-derived integer
  int arr[2] = {10, 20};
  _Bool b3 = arr[0]; // 10 != 0, so b3 = 1

  return b + b2 + b3;  // 1 + 1 + 1 = 3
}

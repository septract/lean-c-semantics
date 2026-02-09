// Test: _Bool conversion (C11 6.3.1.2)
// Any non-zero value converted to _Bool becomes 1
// Audit: C1 - convertInt missing _Bool special case
#include <stdbool.h>
int main(void) {
  // Even values: modular wrapping to [0,1] gives 0, but _Bool should give 1
  _Bool b1 = (_Bool)2;   // 2 != 0, so _Bool = 1
  _Bool b2 = (_Bool)0;   // 0 == 0, so _Bool = 0
  _Bool b3 = (_Bool)255; // 255 != 0, so _Bool = 1
  _Bool b4 = (_Bool)-1;  // -1 != 0, so _Bool = 1
  _Bool b5 = (_Bool)42;  // 42 != 0, so _Bool = 1

  // Sum: 1 + 0 + 1 + 1 + 1 = 4
  return b1 + b2 + b3 + b4 + b5;
}

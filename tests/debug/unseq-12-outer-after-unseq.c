// Outer write AFTER unseq completes - the problematic pattern
// EXPECTED: UB035_unsequenced_race
// This is the x = (x = 1) pattern
int x;

int main(void)
{
  // Inner (x=1) is in an unseq
  // Outer assignment uses the result - outer store is AFTER unseq
  x = (x = 1);
}

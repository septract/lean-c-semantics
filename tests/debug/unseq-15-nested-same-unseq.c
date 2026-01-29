// Nested writes but both results used in SAME outer unseq
// EXPECTED: UB035_unsequenced_race
int x;

int main(void)
{
  // Both writes are in branches of the same outer + unseq
  // Even though each write is in its own inner expression
  ((x = 1) + 0) + ((x = 2) + 0);
}

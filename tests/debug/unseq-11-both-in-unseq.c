// Both writes directly in unseq - should detect race
// EXPECTED: UB035_unsequenced_race
int x;

int main(void)
{
  // Both (x=1) and (x=2) are in the SAME unseq
  (x = 1) + (x = 2);
}

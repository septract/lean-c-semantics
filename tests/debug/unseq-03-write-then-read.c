// Write and read in unseq - should race
// Should be UB035_unsequenced_race (like 0300)
int x;

int main(void)
{
  (x = 1) + x;
}

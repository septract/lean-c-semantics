// Simplest double write - both in unseq directly
// Should be UB035_unsequenced_race
int x;

int main(void)
{
  (x = 1) + (x = 2);
}

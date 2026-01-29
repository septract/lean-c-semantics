// Exact copy of 0301 - x = (x = 1)
// Should be UB035_unsequenced_race
int x;

int main(void)
{
  x = (x = 1);
}

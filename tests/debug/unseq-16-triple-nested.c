// Triple nested - outer assignment uses result of inner which uses another inner
// EXPECTED: UB035_unsequenced_race
int x;

int main(void)
{
  // x = (x = (x = 1))
  // Three writes to x, all should conflict
  x = (x = (x = 1));
}

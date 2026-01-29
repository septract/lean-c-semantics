// Compound assignment - x += (x = 1)
// LHS evaluation unsequenced with RHS side effects
// Should be UB035_unsequenced_race
int x;

int main(void)
{
  x = 0;
  x += (x = 1);  // x += ... reads x, (x=1) writes x
}

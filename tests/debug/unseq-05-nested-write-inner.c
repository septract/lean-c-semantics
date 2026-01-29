// Nested: outer expression assigned to inner
// (x = 1) assigned to x - but written differently
// Should be UB035_unsequenced_race
int x;
int y;

int main(void)
{
  y = (x = 1);  // y = ... doesn't touch x, so inner x=1 is fine
  return y;
}

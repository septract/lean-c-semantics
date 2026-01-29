// Nested: inner expression, outer write
// x = expr where expr writes to x
// Should be UB035_unsequenced_race
int x;

int main(void)
{
  x = (x = 1);  // Same as 0301
}

// Function argument evaluation - unsequenced
// Should be UB035_unsequenced_race
int x;

int f(int a, int b) { return a + b; }

int main(void)
{
  x = 0;
  f(x = 1, x = 2);  // Args unsequenced, both write x
}

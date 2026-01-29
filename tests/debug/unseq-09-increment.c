// Classic i = i++ case
// Should be UB035_unsequenced_race
int i;

int main(void)
{
  i = 0;
  i = i++;  // Read i (for ++), write i (++), write i (=)
}

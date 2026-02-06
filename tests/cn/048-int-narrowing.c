// CN test: Integer narrowing cast with range constraints
// From cn-tutorial: int_to_char_1.c
// Tests: CN built-in functions MINu8()/MAXu8(), integer casts in spec
// NEEDS: MINu8()/MAXu8() builtins, spec casts (i32)

void int_to_char(int a)
/*@ requires
      (i32) MINu8() <= (i32) a;
      (i32) a <= (i32) MAXu8(); @*/
{
  char b;
  b = a;
  return;
}

int main(void)
{
  int_to_char(65);
  return 0;
}

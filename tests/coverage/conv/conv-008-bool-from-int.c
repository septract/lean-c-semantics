// Test: int to _Bool conversion
// Exercises: PEconv_int integer-to-bool (0 -> false, nonzero -> true)
int main(void) {
  _Bool b0 = 0;
  _Bool b1 = 42;
  _Bool b2 = -1;
  if (b0 != 0) return 1;
  if (b1 != 1) return 2;
  if (b2 != 1) return 3;
  return 0;
}

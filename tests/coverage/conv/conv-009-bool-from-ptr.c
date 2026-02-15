// Test: pointer to _Bool conversion
// Exercises: PEconv_int/PEconv_loaded_int pointer-to-bool (non-null -> true)
int main(void) {
  int x = 0;
  _Bool b = &x;
  return b == 1 ? 0 : 1;
}

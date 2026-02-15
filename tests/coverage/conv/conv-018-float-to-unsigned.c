// Test: double to unsigned int conversion
// Exercises: PEconv_int float-to-unsigned (truncation toward zero)
int main(void) {
  double d = 42.9;
  unsigned int u = (unsigned int)d;
  return u == 42 ? 0 : 1;
}

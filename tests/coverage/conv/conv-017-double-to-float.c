// Test: double to float narrowing
// Exercises: PEconv_int/floating double-to-float narrowing conversion
int main(void) {
  double d = 1.23456789012345;
  float f = (float)d;
  // f loses precision; verify it round-trips differently
  double back = (double)f;
  // back != d due to precision loss
  return (back != d) ? 0 : 1;
}

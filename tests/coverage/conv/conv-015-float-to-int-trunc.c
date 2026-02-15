// Test: double to int truncation
// Exercises: PEconv_int float-to-int conversion (truncation toward zero)
int main(void) {
  double d = 3.7;
  int x = (int)d;
  return x == 3 ? 0 : 1;
}

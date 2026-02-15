// Test: _Generic with multiple type associations
// Exercises: PEare_compatible — multiple type compatibility checks
int main(void) {
  float f = 1.0f;
  double d = 2.0;
  int r1 = _Generic(f, float: 0, double: 1, default: 2);
  int r2 = _Generic(d, float: 1, double: 0, default: 2);
  return r1 + r2;
}

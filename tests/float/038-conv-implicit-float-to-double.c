// Test: implicit float to double in mixed arithmetic
int main(void) {
  float a = 1.5f;
  double b = 2.5;
  double c = a + b;  // a is implicitly converted to double
  return (c == 4.0) ? 0 : 1;
}

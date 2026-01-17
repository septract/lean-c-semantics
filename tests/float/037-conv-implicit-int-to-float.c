// Test: implicit int to float in mixed arithmetic
int main(void) {
  int a = 2;
  float b = 3.0f;
  float c = a + b;  // a is implicitly converted to float
  return (c == 5.0f) ? 0 : 1;
}

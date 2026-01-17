// Test: float less-or-equal comparison
int main(void) {
  float a = 1.0f;
  float b = 1.0f;
  int r1 = (a <= b);  // true
  float c = 0.5f;
  int r2 = (c <= b);  // true
  return (r1 && r2) ? 0 : 1;
}

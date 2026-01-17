// Test: float to double promotion
int main(void) {
  float a = 1.5f;
  double b = (double)a;
  return (b == 1.5) ? 0 : 1;
}

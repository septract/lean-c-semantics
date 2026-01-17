// Test: double to float narrowing
int main(void) {
  double a = 2.5;
  float b = (float)a;
  return (b == 2.5f) ? 0 : 1;
}

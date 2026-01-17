// Test: float passed as function parameter
float identity(float x) {
  return x;
}

int main(void) {
  float a = 3.5f;
  float b = identity(a);
  return (b == 3.5f) ? 0 : 1;
}

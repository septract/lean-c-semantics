// Test: logical OR with floats
int main(void) {
  float a = 0.0f;
  float b = 2.0f;
  int result = a || b;  // Should be 1 (true)
  return (result == 1) ? 0 : 1;
}

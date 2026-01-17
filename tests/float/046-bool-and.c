// Test: logical AND with floats
int main(void) {
  float a = 1.0f;
  float b = 2.0f;
  int result = a && b;  // Should be 1 (true)
  return (result == 1) ? 0 : 1;
}

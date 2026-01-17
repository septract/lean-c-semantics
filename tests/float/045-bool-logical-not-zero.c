// Test: logical NOT on zero float
int main(void) {
  float a = 0.0f;
  int result = !a;  // Should be 1 (true)
  return (result == 1) ? 0 : 1;
}

// Test: float zero is false in boolean context
int main(void) {
  float a = 0.0f;
  if (a) {
    return 1;  // Should not reach here
  }
  return 0;
}

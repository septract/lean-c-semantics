// Test: double non-zero is true in boolean context
int main(void) {
  double a = 1.0;
  if (a) {
    return 0;  // Should reach here
  }
  return 1;
}

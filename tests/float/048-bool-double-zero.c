// Test: double zero is false in boolean context
int main(void) {
  double a = 0.0;
  if (a) {
    return 1;  // Should not reach here
  }
  return 0;
}

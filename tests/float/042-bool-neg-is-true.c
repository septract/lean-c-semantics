// Test: negative float is true in boolean context
int main(void) {
  float a = -1.0f;
  if (a) {
    return 0;  // Should reach here
  }
  return 1;
}

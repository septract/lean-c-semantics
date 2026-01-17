// Test: very small float is still true in boolean context
int main(void) {
  float a = 0.000001f;
  if (a) {
    return 0;  // Should reach here
  }
  return 1;
}

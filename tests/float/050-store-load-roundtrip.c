// Test: basic float store/load roundtrip through memory
int main(void) {
  float a = 1.0f;
  float b = a;  // Should preserve value through memory
  return (b == 1.0f) ? 0 : 1;
}

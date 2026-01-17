// Test: fractional float store/load roundtrip
int main(void) {
  float a = 0.125f;  // Exact binary fraction (1/8)
  float b = a;
  return (b == 0.125f) ? 0 : 1;
}

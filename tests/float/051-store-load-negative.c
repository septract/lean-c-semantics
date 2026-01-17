// Test: negative float store/load roundtrip
int main(void) {
  float a = -42.5f;
  float b = a;
  return (b == -42.5f) ? 0 : 1;
}

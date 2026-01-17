// Test: large float value
int main(void) {
  float a = 1000000.0f;
  float b = a;
  return (b == 1000000.0f) ? 0 : 1;
}

// Test: negative float to int conversion (truncation toward zero)
int main(void) {
  float a = -3.7f;
  int b = (int)a;
  return (b == -3) ? 0 : 1;
}

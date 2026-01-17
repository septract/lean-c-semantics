// Test: float postfix increment
int main(void) {
  float a = 1.0f;
  float b = a++;
  // b should be old value (1.0), a should be new value (2.0)
  return (b == 1.0f && a == 2.0f) ? 0 : 1;
}

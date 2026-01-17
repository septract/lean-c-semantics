// Test: float postfix decrement
int main(void) {
  float a = 3.0f;
  float b = a--;
  // b should be old value (3.0), a should be new value (2.0)
  return (b == 3.0f && a == 2.0f) ? 0 : 1;
}

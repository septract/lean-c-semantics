// Test: ternary operator with float result
int main(void) {
  int cond = 1;
  float a = cond ? 2.5f : 3.5f;
  return (a == 2.5f) ? 0 : 1;
}

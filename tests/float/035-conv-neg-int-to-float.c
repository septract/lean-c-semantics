// Test: negative int to float conversion
int main(void) {
  int a = -10;
  float b = (float)a;
  return (b == -10.0f) ? 0 : 1;
}

// Test: unsigned int to float conversion
int main(void) {
  unsigned int a = 100;
  float b = (float)a;
  return (b == 100.0f) ? 0 : 1;
}

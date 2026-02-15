// Test: unsigned char to int zero extension
// Exercises: PEconv_int widening with zero extension
int main(void) {
  unsigned char c = 255;
  int x = c;
  return x == 255 ? 0 : 1;
}

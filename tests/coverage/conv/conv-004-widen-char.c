// Test: signed char to int sign extension
// Exercises: PEconv_int widening with sign extension
int main(void) {
  signed char c = -1;
  int x = c;
  return x == -1 ? 0 : 1;
}

// Test: int to long widening conversion
// Exercises: PEconv_int widening (int to long, preserves sign)
int main(void) {
  int x = -42;
  long l = x;
  return l == -42 ? 0 : 1;
}

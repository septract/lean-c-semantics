// Test: integer promotion in arithmetic
// Exercises: PEconv_int implicit promotion (short -> int before addition)
int main(void) {
  short a = 30000;
  short b = 30000;
  int c = a + b;
  return c == 60000 ? 0 : 1;
}

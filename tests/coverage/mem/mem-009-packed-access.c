// Test: struct member access at various alignments
// Exercises: impl_mem.ml alignment calculations for mixed-type struct members
struct mixed {
  char a;
  int b;
  short c;
  char d;
  long e;
};

int main(void) {
  struct mixed m;
  m.a = 1;
  m.b = 100;
  m.c = 200;
  m.d = 3;
  m.e = 400;
  int result = m.a + m.b + m.c + m.d + (int)m.e;
  // 1 + 100 + 200 + 3 + 400 = 704
  return (result == 704) ? 0 : 1;
}

// Test: struct with many members of various types
// Exercises: impl_mem.ml sizeof/alignof calculation and multi-field member access
struct big {
  char a;
  short b;
  int c;
  long d;
  char e;
  int f;
  short g;
  char h;
  long i;
  int j;
  char k;
  short l;
};

int main(void) {
  struct big s;
  s.a = 1;
  s.b = 2;
  s.c = 3;
  s.d = 4;
  s.e = 5;
  s.f = 6;
  s.g = 7;
  s.h = 8;
  s.i = 9;
  s.j = 10;
  s.k = 11;
  s.l = 12;
  int sum = s.a + s.b + s.c + s.d + s.e + s.f
          + s.g + s.h + s.i + s.j + s.k + s.l;
  // 1+2+3+4+5+6+7+8+9+10+11+12 = 78
  return (sum == 78) ? 0 : 1;
}

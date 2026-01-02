// Minimal: union basic
union U {
  int i;
  int j; // Overlaps exactly with i
};

int main(void) {
  union U u;
  u.i = 123;
  return u.j; // 123
}

// Minimal: sizeof expression (struct)
struct Point {
  int x;
  int y;
};

int main(void) {
  struct Point p;
  // Size should be at least 2*sizeof(int).
  // We just check it evaluates.
  int size = sizeof(p);
  return (size >= 2) ? 1 : 0;
}

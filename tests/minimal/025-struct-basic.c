// Minimal: struct member access
struct Point {
  int x;
  int y;
};

int main(void) {
  struct Point p;
  p.x = 10;
  p.y = 20;
  return p.x + p.y;  // 30
}

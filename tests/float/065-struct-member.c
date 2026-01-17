// Test: float as struct member
struct Point {
  float x;
  float y;
};

int main(void) {
  struct Point p;
  p.x = 1.0f;
  p.y = 2.0f;
  return (p.x + p.y == 3.0f) ? 0 : 1;
}

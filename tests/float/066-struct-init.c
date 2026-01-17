// Test: struct with float initializer
struct Point {
  float x;
  float y;
};

int main(void) {
  struct Point p = {3.0f, 4.0f};
  return (p.x == 3.0f && p.y == 4.0f) ? 0 : 1;
}

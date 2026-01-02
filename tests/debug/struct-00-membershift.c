// Debug: just member shift and load
struct Data { int x; };

int main(void) {
  struct Data d;
  d.x = 42;
  return d.x; // Should be 42
}

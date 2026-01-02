// Debug: struct initialization only
struct Data { int x; };

int main(void) {
  struct Data d = {42};
  return d.x; // Should be 42
}

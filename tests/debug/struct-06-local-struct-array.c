// Test: struct with array, accessed locally (no function call)
struct s { int f[2]; };

int main() {
  struct s s = { 10, 20 };
  return s.f[0] + s.f[1];
}

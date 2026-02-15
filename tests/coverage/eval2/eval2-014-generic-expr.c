// Test: _Generic expression for type dispatch
// Exercises: PEare_compatible — type compatibility check in evaluator
int main(void) {
  int x = 42;
  int r = _Generic(x, int: 0, default: 1);
  return r;
}

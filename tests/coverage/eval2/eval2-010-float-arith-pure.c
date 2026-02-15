// Test: float addition in pure expression context
// Exercises: float arithmetic (OpAdd) in evaluator
int main(void) {
  float a = 1.5f;
  float b = 2.5f;
  float c = a + b;
  return (int)c == 4 ? 0 : 1;
}

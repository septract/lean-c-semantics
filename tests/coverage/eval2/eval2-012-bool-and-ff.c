// Test: boolean AND with false operands
// Exercises: OpAnd boolean operation in evaluator
int main(void) {
  _Bool a = 0;
  _Bool b = 0;
  _Bool c = a && b;
  return c == 0 ? 0 : 1;
}

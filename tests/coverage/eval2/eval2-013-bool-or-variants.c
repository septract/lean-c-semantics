// Test: boolean OR with all four input combinations
// Exercises: OpOr boolean operation in evaluator
int main(void) {
  _Bool r1 = (_Bool)0 || (_Bool)0;
  _Bool r2 = (_Bool)0 || (_Bool)1;
  _Bool r3 = (_Bool)1 || (_Bool)0;
  _Bool r4 = (_Bool)1 || (_Bool)1;
  return (r1 == 0 && r2 == 1 && r3 == 1 && r4 == 1) ? 0 : 1;
}

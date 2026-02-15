// Exercises: process_impl_proc -> BuiltinFunction "ctz"
// in core_reduction.lem lines 1008-1021.
// __builtin_ctz returns the number of trailing zero bits. Undefined for 0.
int main(void) {
  int a = __builtin_ctz(8);  // 8 = 0b1000, trailing zeros = 3
  int b = __builtin_ctz(1);  // 1 = 0b0001, trailing zeros = 0
  if (a != 3) return 1;
  if (b != 0) return 2;
  return 0;
}

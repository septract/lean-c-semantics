// Exercises: process_impl_proc -> BuiltinFunction "generic_ffs"
// in core_reduction.lem lines 993-1006.
// __builtin_ffs returns 1 + index of least significant set bit, or 0 if input is 0.
int main(void) {
  int a = __builtin_ffs(0);   // expected: 0
  int b = __builtin_ffs(12);  // 12 = 0b1100, lowest set bit is bit 2 (0-indexed), returns 3
  if (a != 0) return 1;
  if (b != 3) return 2;
  return 0;
}

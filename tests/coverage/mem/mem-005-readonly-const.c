// Test: attempt to write to const variable via pointer cast (UB)
// Exercises: impl_mem.ml read-only / const check path
// Expected: Cerberus detects UB (modifying const object)
int main(void) {
  const int x = 42;
  int *p = (int *)&x;
  *p = 99;
  return *p;
}

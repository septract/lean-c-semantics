// Test: read an uninitialized local variable (UB)
// Exercises: impl_mem.ml uninitialized memory detection path
// Expected: Cerberus detects UB (reading uninitialized memory)
int main(void) {
  int x;
  return x;
}

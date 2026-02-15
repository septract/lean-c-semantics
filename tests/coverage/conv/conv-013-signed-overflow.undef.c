// Test: signed integer overflow (undefined behavior)
// Exercises: PEcatch_exceptional_condition for signed overflow
// This is UB - Cerberus should detect it
int main(void) {
  int x = 2147483647;
  x = x + 1;
  return x;
}

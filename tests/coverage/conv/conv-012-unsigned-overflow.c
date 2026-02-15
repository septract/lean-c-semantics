// Test: unsigned integer wrapping (well-defined)
// Exercises: PEwrapI unsigned modular arithmetic
int main(void) {
  unsigned int u = 0;
  u = u - 1;
  return u == 4294967295U ? 0 : 1;
}

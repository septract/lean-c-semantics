// Test: 2-byte store and load
// Exercises: impl_mem.ml store/load path for short type
int main(void) {
  short s = 1234;
  short t = s;
  return (t == 1234) ? 0 : 1;
}

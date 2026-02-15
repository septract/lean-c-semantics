// Test: byte-level store and load
// Exercises: impl_mem.ml store/load path for char type
int main(void) {
  char c = 'A';
  char d = c;
  return (d == 'A') ? 0 : 1;
}

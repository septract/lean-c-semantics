// Test: negative int to unsigned conversion
// Exercises: PEconv_int signed-to-unsigned (modular reduction)
int main(void) {
  int x = -1;
  unsigned int u = x;
  return u == 4294967295U ? 0 : 1;
}

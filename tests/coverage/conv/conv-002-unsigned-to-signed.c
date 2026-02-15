// Test: large unsigned to signed conversion (impl-defined)
// Exercises: PEconv_int unsigned-to-signed overflow path
int main(void) {
  unsigned int u = 4294967295U;
  int x = u;
  // Implementation-defined: typically -1 on two's complement
  return x == -1 ? 0 : 1;
}

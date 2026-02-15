// Test: write bytes via unsigned char* then read as int
// Exercises: impl_mem.ml byte-level store through char pointer, then load as int
int main(void) {
  int x;
  unsigned char *p = (unsigned char *)&x;
  for (int i = 0; i < (int)sizeof(int); i++) {
    p[i] = 0;
  }
  return (x == 0) ? 0 : 1;
}

// Test: read int via char* (well-defined type punning)
// Exercises: impl_mem.ml byte-level load through char pointer aliasing
int main(void) {
  int x = 0x01020304;
  unsigned char *p = (unsigned char *)&x;
  int sum = 0;
  for (int i = 0; i < (int)sizeof(int); i++) {
    sum += p[i];
  }
  // Sum of bytes of 0x01020304 = 1+2+3+4 = 10
  return (sum == 10) ? 0 : 1;
}

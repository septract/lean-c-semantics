// Test: multiple chained casts
// Exercises: PEconv_int through multiple type widths
int main(void) {
  char c = 'A';        // 65
  int i = c;           // char -> int
  long l = i;          // int -> long
  short s = (short)l;  // long -> short
  return s == 65 ? 0 : 1;
}

// Test: long to int narrowing conversion
// Exercises: PEconv_int narrowing (long to int)
int main(void) {
  long l = 100L;
  int x = l;
  return x == 100 ? 0 : 1;
}

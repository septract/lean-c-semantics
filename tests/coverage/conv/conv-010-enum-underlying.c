// Test: enum to int and int to enum conversion
// Exercises: PEconv_int enum underlying type conversions
enum color { RED = 0, GREEN = 1, BLUE = 2 };

int main(void) {
  enum color c = GREEN;
  int i = c;
  if (i != 1) return 1;
  enum color c2 = 2;
  if (c2 != BLUE) return 2;
  return 0;
}

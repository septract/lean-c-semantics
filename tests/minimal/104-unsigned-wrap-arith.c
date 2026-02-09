// Test: unsigned arithmetic wrapping
// Unsigned overflow wraps modularly (not UB)
// Exercises wrapIntOp for non-division operations
int main(void) {
  unsigned char a = 250;
  unsigned char b = 10;
  unsigned char sum = a + b;  // 260 % 256 = 4

  unsigned char c = 0;
  unsigned char d = 1;
  unsigned char diff = c - d;  // -1 wraps to 255

  // 4 + 255 = 259, return as int
  return (int)sum + (int)diff;  // 259, exit truncates mod 256 = 3
}

// Minimal: type casting (int to char)
int main(void) {
  int x = 0xABC; // 2748
  // Cast to char (usually 8-bit), masking to 0xBC.
  // We mask the result with 0xFF to ensure we get a positive value for the exit code.
  return (char)x & 0xFF;  // 0xBC = 188
}
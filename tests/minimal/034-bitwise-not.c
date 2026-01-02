// Minimal: bitwise NOT
int main(void) {
  // ~0 is -1, which is 0xFFFFFFFF in 32-bit two's complement.
  // We mask it to keep the result positive and small for exit codes.
  return (~0) & 0xFF;  // 255
}

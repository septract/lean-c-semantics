// Test: Simple conv_int - what does -1 become as unsigned long?
// Return low bits to check (can't return full 64-bit value)
int main(void) {
  unsigned long x = (unsigned long)(-1);
  // If correct, x = ULONG_MAX = 0xFFFFFFFFFFFFFFFF
  // Low 8 bits should be 0xFF = 255
  return (int)(x & 0xFF);
}

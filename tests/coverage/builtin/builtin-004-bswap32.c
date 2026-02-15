// Exercises: process_impl_proc -> BuiltinFunction "bswap32"
// in core_reduction.lem lines 1039-1052.
// __builtin_bswap32 reverses the bytes of a 32-bit value.
int main(void) {
  unsigned int x = __builtin_bswap32(0x12345678u);
  // 0x12345678 byte-swapped => 0x78563412
  if (x != 0x78563412u) return 1;
  return 0;
}

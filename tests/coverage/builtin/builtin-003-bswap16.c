// Exercises: process_impl_proc -> BuiltinFunction "bswap16"
// in core_reduction.lem lines 1024-1037.
// __builtin_bswap16 reverses the bytes of a 16-bit value.
int main(void) {
  unsigned short x = __builtin_bswap16(0x1234);
  // 0x1234 byte-swapped => 0x3412
  if (x != 0x3412) return 1;
  return 0;
}

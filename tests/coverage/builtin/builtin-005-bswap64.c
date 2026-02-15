// Exercises: process_impl_proc -> BuiltinFunction "bswap64"
// in core_reduction.lem lines 1054-1067.
// __builtin_bswap64 reverses the bytes of a 64-bit value.
int main(void) {
  unsigned long long x = __builtin_bswap64(0x0102030405060708ULL);
  // byte-swapped => 0x0807060504030201
  if (x != 0x0807060504030201ULL) return 1;
  return 0;
}

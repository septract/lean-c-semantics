// Exercises: process_impl_proc -> BuiltinFunction "exit"
// in core_reduction.lem lines 976-991.
// exit() terminates the program with the given status code.
// Requires libc (stdlib.h).
#include <stdlib.h>

int main(void) {
  exit(42);
  return 1;  // unreachable
}

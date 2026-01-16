// Test: _Bool trap representation
// Loading a _Bool with value other than 0 or 1 is UB (trap representation)
// Expected: UB detected (MerrTrapRepresentation)
#include <stdbool.h>

int main(void) {
    unsigned char c = 2;  // Not 0 or 1
    _Bool *bp = (_Bool *)&c;
    _Bool b = *bp;  // UB: trap representation
    return b;
}

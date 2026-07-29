// Ported from CN test suite: array_shift_mismatch.error.c
#include <inttypes.h>

int *f(int *p)
/*@
requires
    !is_null(p);
ensures
    ptr_eq(return,array_shift<void>(p, 1u64));
@*/
{
    return p + 1;
}

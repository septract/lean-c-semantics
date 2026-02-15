// ptr3-007-null-lt-null.c
// Exercise le_ptrval/lt_ptrval PVnull cases in impl_mem.ml (L1890-1950)
// Comparing null pointers relationally - this may be UB but exercises the path
int main(void) {
    int *p = (int*)0;
    int *q = (int*)0;
    int r1 = (p < q);  // lt_ptrval with PVnull
    int r2 = (p <= q); // le_ptrval with PVnull
    (void)r1;
    (void)r2;
    return 0;
}

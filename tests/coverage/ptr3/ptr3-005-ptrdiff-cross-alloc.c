// ptr3-005-ptrdiff-cross-alloc.c
// Exercise diff_ptrval error_postcond for different allocations (UB)
// This is UB but still generates coverage data
int main(void) {
    int a[5];
    int b[5];
    int *p = &a[0];
    int *q = &b[0];
    int diff = (int)(p - q); // UB: different allocations
    (void)diff;
    return 0;
}

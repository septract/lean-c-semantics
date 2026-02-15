// ptr2-010-eff-zero-shift.c
// Pointer arithmetic with zero offset (edge case).
// Exercises eff_array_shift_ptrval with offset 0.
// Expected return: 99
int main(void) {
    int x = 99;
    int *p = &x;
    return *(p + 0);
}

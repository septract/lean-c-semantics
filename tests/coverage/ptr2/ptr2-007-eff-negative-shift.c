// ptr2-007-eff-negative-shift.c
// Negative pointer offset via pointer arithmetic.
// Exercises eff_array_shift_ptrval with a negative shift amount.
// Expected return: 20
int main(void) {
    int a[5];
    a[0] = 10;
    a[1] = 20;
    a[2] = 30;
    a[3] = 40;
    a[4] = 50;
    int *p = &a[3];
    return *(p - 2);
}

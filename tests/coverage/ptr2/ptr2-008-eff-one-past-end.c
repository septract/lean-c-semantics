// ptr2-008-eff-one-past-end.c
// Create a one-past-the-end pointer via pointer arithmetic.
// Exercises eff_array_shift_ptrval for the boundary case.
// Expected return: 0
int main(void) {
    int a[5];
    int *p = a + 5;
    return p == &a[5] ? 0 : 1;
}

// ptr2-011-funcptr-eq.c
// Function pointer equality comparison (same function).
// Exercises eq_ptrval funcptr branch (0% covered) in impl_mem.ml.
// Expected return: 0
int f(void) { return 1; }

int main(void) {
    return &f == &f ? 0 : 1;
}

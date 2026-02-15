// ptr2-012-funcptr-ne.c
// Function pointer inequality comparison (different functions).
// Exercises eq_ptrval / ne_ptrval funcptr branch in impl_mem.ml.
// Expected return: 0
int f(void) { return 1; }
int g(void) { return 2; }

int main(void) {
    return &f != &g ? 0 : 1;
}

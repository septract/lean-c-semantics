// ptr-007-func-ptr-compare.c
// Function pointer equality comparison.
// Exercises: impl_mem.ml function pointer comparison path
// Expected: exit 0
int f(void) { return 1; }
int g(void) { return 2; }

int main(void) {
    int (*pf)(void) = &f;
    int (*pg)(void) = &g;
    // f and g are different functions, so pf != pg
    return pf != pg ? 0 : 1;
}

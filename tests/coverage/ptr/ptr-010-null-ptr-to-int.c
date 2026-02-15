// ptr-010-null-ptr-to-int.c
// Cast NULL pointer to integer.
// Exercises: impl_mem.ml null pointer to integer conversion
// Expected: exit 0
int main(void) {
    unsigned long i = (unsigned long)(void *)0;
    return i == 0 ? 0 : 1;
}

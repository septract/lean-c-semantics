// ptr-009-ptr-to-int-roundtrip.c
// Pointer to integer to pointer roundtrip.
// Exercises: impl_mem.ml ptrToInt and intToPtr (PtrToInt/IntToPtr casts)
// Expected: exit 42
int main(void) {
    int x = 42;
    unsigned long i = (unsigned long)&x;
    int *p = (int *)i;
    return *p;
}

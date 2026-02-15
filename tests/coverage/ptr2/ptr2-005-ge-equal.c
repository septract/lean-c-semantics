// ptr2-005-ge-equal.c
// Pointer greater-than-or-equal on identical pointers (reflexive case).
// Exercises ge_ptrval with equal pointers.
// Expected return: 0
int main(void) {
    int x;
    int *p = &x;
    return p >= p ? 0 : 1;
}

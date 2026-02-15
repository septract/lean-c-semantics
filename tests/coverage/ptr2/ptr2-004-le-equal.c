// ptr2-004-le-equal.c
// Pointer less-than-or-equal on identical pointers (reflexive case).
// Exercises le_ptrval with equal pointers.
// Expected return: 0
int main(void) {
    int x;
    int *p = &x;
    return p <= p ? 0 : 1;
}

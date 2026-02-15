// ptr-003-compare-equality.c
// Pointer equality comparison (same object).
// Exercises: impl_mem.ml pointer equality (op_ival EQ)
// Expected: exit 0
int main(void) {
    int x;
    int *p = &x;
    int *q = &x;
    return p == q ? 0 : 1;
}

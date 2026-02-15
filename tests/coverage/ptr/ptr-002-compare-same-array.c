// ptr-002-compare-same-array.c
// Pointer relational comparison within an array.
// Exercises: impl_mem.ml pointer relational comparison (op_ival LT)
// Expected: exit 0
int main(void) {
    int a[5];
    return &a[1] < &a[3] ? 0 : 1;
}

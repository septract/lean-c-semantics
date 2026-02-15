// ptr-001-subtract-same-array.c
// Pointer subtraction within an array.
// Exercises: impl_mem.ml pointer difference (op_ival DIFF)
// Expected: exit 3
int main(void) {
    int a[5];
    int *p = &a[1];
    int *q = &a[4];
    return q - p;
}

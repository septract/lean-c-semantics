// ptr2-002-ge-same-array.c
// Pointer greater-than-or-equal comparison within same array.
// Exercises ge_ptrval (0% covered in impl_mem.ml).
// Expected return: 0
int main(void) {
    int a[5];
    return &a[3] >= &a[1] ? 0 : 1;
}

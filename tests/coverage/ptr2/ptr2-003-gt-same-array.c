// ptr2-003-gt-same-array.c
// Pointer greater-than comparison within same array.
// Exercises gt_ptrval (0% covered in impl_mem.ml).
// Expected return: 0
int main(void) {
    int a[5];
    return &a[3] > &a[1] ? 0 : 1;
}

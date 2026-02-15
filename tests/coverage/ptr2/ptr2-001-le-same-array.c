// ptr2-001-le-same-array.c
// Pointer less-than-or-equal comparison within same array.
// Exercises le_ptrval (0% covered in impl_mem.ml).
// Expected return: 0
int main(void) {
    int a[5];
    return &a[1] <= &a[3] ? 0 : 1;
}

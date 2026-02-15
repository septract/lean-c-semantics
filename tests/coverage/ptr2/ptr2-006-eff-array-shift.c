// ptr2-006-eff-array-shift.c
// Array indexing with a computed (non-constant) index.
// The variable index forces an effectful array shift via
// eff_array_shift_ptrval (0% covered in impl_mem.ml).
// Expected return: 25 (5*5)
int main(void) {
    int arr[10];
    for (int i = 0; i < 10; i++)
        arr[i] = i * i;
    int j = 5;
    return arr[j];
}

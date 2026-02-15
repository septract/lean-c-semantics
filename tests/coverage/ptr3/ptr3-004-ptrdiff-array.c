// ptr3-004-ptrdiff-array.c
// Exercise diff_ptrval valid_postcond with array type in impl_mem.ml (L1963)
int main(void) {
    int a[10];
    int *p = &a[7];
    int *q = &a[2];
    int diff = (int)(p - q); // pointer subtraction
    if (diff != 5) return 1;
    // Reverse direction
    int diff2 = (int)(q - p);
    if (diff2 != -5) return 2;
    return 0;
}

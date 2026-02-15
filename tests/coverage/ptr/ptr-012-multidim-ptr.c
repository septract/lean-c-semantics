// ptr-012-multidim-ptr.c
// Pointer arithmetic on 2D array.
// Exercises: impl_mem.ml multi-dimensional array pointer arithmetic
// Expected: exit 0
int main(void) {
    int a[2][3] = {{1, 2, 3}, {4, 5, 6}};
    int *p = &a[0][0];
    return p[4] == 5 ? 0 : 1;
}

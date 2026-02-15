// ptr-011-array-decay.c
// Array-to-pointer decay.
// Exercises: impl_mem.ml array decay and pointer indexing
// Expected: exit 0
int main(void) {
    int a[3] = {10, 20, 30};
    int *p = a;
    return p[1] == 20 ? 0 : 1;
}

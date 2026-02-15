// mem3-006-array-of-ptrs.c
// Exercise taint merging with array of pointers
int main(void) {
    int vals[4] = {10, 20, 30, 40};
    int *ptrs[4];
    for (int i = 0; i < 4; i++)
        ptrs[i] = &vals[i];
    // Read back through the pointer array
    int sum = 0;
    for (int i = 0; i < 4; i++)
        sum += *ptrs[i];
    if (sum != 100) return 1;
    return 0;
}

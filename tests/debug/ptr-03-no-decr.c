// No decrement - just point and dereference
int main(void) {
    int a[] = {10, 20, 30};
    int *p = &a[1];  // point to a[1]
    return *p;       // should return 20
}

// Test simple pointer reassignment
int main(void) {
    int a[] = {10, 20, 30};
    int *p = &a[2];  // p points to a[2] (30)
    p = &a[1];       // reassign p to point to a[1] (20)
    return *p;       // should return 20
}

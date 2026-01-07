// Simplest pointer decrement test
int main(void) {
    int a[] = {10, 20, 30};
    int *p = &a[2];  // point to a[2]
    p--;             // decrement to a[1]
    return *p;       // should return 20
}

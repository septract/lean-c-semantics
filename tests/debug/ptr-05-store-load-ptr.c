// Test storing and loading pointer through a pointer variable
int main(void) {
    int a[] = {10, 20, 30};
    int *p = &a[1];  // store pointer to a[1] in p
    int *q = p;      // load p into q
    return *q;       // should return 20
}

// Test explicit pointer subtraction (not using --)
int main(void) {
    int a[] = {10, 20, 30};
    int *p = &a[2];  // point to a[2]
    p = p - 1;       // explicit subtraction
    return *p;       // should return 20
}

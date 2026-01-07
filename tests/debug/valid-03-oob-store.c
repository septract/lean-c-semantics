// Test: store to out-of-bounds pointer
// Expected: UB
int a[10];
int main(void) {
    a[10] = 42;  // UB: write one-past-end
    return 0;
}

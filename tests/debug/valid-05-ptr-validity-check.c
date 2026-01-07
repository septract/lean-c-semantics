// Test: PtrValidForDeref memop directly
// This mirrors what Core generates for lvalue evaluation
// Expected: clean exit (validity check returns false, but no UB)
int a[10];
int main(void) {
    int *p = &a[10];  // one-past-end pointer
    // In Core: memop(PtrValidForDeref, 'int', p) returns false
    // But computing this should not be UB by itself
    return 0;
}

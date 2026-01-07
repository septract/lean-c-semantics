// Test one-past-the-end pointer arithmetic
// The pointer i = &a[3] should be valid (one past end) and have provenance
int main(void) {
    int a[] = {0, 1, 2};
    int *i = &a[3];  // one-past-the-end, valid for comparison but not deref

    // Decrement to point to valid element
    i--;

    // This should be valid: i now points to a[2]
    return *i;  // should return 2
}

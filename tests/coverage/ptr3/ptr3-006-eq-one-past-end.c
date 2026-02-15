// ptr3-006-eq-one-past-end.c
// Exercise eq_ptrval provenance mismatch in impl_mem.ml (L1871-1879)
int main(void) {
    int a[5];
    int b;
    int *p = &a[5]; // one-past-end of a
    int *q = &b;
    // Equality comparison with different provenance
    int eq = (p == q);
    (void)eq;
    return 0;
}

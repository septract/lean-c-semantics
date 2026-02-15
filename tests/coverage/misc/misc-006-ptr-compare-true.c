// misc-006-ptr-compare-true.c
// Exercise PtrGt/PtrLe/PtrGe true branches in driver.ml (L740,744,748)
// Need pointer comparisons where each relation returns both true and false
int main(void) {
    int a[3] = {10, 20, 30};
    int *lo = &a[0];
    int *hi = &a[2];
    // Test all relational operators in both true and false directions
    if (!(hi > lo))  return 1;  // gt true
    if (lo > hi)     return 2;  // gt false
    if (!(lo <= hi)) return 3;  // le true
    if (hi <= lo)    return 4;  // le false
    if (!(hi >= lo)) return 5;  // ge true
    if (lo >= hi)    return 6;  // ge false
    // Equal pointers
    int *p = &a[1];
    int *q = &a[1];
    if (!(p <= q)) return 7;  // le true (equal)
    if (!(p >= q)) return 8;  // ge true (equal)
    return 0;
}

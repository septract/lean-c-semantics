// ptr3-008-null-le-null.c
// Exercise ge_ptrval/gt_ptrval PVnull cases
int main(void) {
    int *p = (int*)0;
    int *q = (int*)0;
    int r1 = (p > q);  // gt_ptrval with PVnull
    int r2 = (p >= q); // ge_ptrval with PVnull
    (void)r1;
    (void)r2;
    return 0;
}

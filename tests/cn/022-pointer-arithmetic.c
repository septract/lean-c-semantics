// Test: Pointer arithmetic - accessing array elements
// Tests arrayShift/memberShift handling

int array_access(int *arr, int idx)
/*@ requires take v = Owned<signed int>(arr + idx);
    ensures take v2 = Owned<signed int>(arr + idx);
            return == v;
            v == v2; @*/
{
    return *(arr + idx);
}

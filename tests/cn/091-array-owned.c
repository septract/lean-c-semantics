// Test: Array element access via Owned with pointer arithmetic
// Takes ownership of individual array elements and reads one

int read_arr_elem(int *arr)
/*@ requires take v0 = Owned<int>(arr);
             take v1 = Owned<int>(arr + 1i32);
    ensures take w0 = Owned<int>(arr);
            take w1 = Owned<int>(arr + 1i32);
            return == v1;
            v0 == w0;
            v1 == w1; @*/
{
    return *(arr + 1);
}

int main(void)
{
    int a[2] = {10, 20};
    return read_arr_elem(a);
}

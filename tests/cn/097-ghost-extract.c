// Test: focus (formerly extract) from each - extract a single element from
// an iterated resource to access it individually

int read_elem(int *arr, int n)
/*@ requires take elems = each (u64 i; 0u64 <= i && i < 3u64)
                               {Owned<int>(array_shift(arr, i))};
    ensures take elems2 = each (u64 i; 0u64 <= i && i < 3u64)
                               {Owned<int>(array_shift(arr, i))};
            return == elems[1u64]; @*/
{
    /*@ focus Owned<int>, 1u64; @*/
    return arr[1];
}

int main(void)
/*@ trusted; @*/
{
    int a[3] = {10, 20, 30};
    return read_elem(a, 3);
}

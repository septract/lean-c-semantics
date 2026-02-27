// Test: Pointer-to-integer conversion (NULL case)
// Cast NULL pointer to unsigned long long, result should be 0

unsigned long long null_to_int(int *p)
/*@ requires ptr_eq(p, NULL);
    ensures return == 0u64; @*/
{
    return (unsigned long long)p;
}

int main(void)
{
    return (int)null_to_int((int *)0);
}

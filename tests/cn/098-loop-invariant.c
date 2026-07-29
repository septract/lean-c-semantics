// Test: While loop with invariant
// Sums integers from 0 to n-1 using a loop with CN invariant

int sum_to(int n)
/*@ requires n >= 0i32; n <= 100i32;
    ensures return >= 0i32; @*/
{
    int acc = 0;
    int i = 0;
    while (i < n)
    /*@ inv 0i32 <= i; i <= n;
            0i32 <= acc;
            n >= 0i32; n <= 100i32; @*/
    {
        acc = acc + i;
        i = i + 1;
    }
    return acc;
}

int main(void)
/*@ trusted; @*/
{
    return sum_to(10);
}

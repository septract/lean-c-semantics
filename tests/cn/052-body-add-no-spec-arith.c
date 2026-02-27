// Test: body has x + 1, but spec has no arithmetic (only Owned)
// Isolates: body-side binop type propagation without spec arithmetic
void inc_ptr(int *p)
/*@ requires take v = Owned<int>(p);
             v <= 2147483646i32;
    ensures take v2 = Owned<int>(p); @*/
{
    *p = *p + 1;
}

int main(void)
{
    int x = 0;
    inc_ptr(&x);
    return x;
}

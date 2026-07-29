// Test: Ghost function parameters (cn_ghost)
// Ghost parameters are provided at call site in /*@ ... @*/ annotations
// and are available in the spec but not in the C code

int check_sum(int total)
/*@ requires cn_ghost i32 a, i32 b;
             a + b == total;
             a >= 0i32; b >= 0i32;
             total >= 0i32; total <= 1000i32;
    ensures return == a + b; @*/
{
    return total;
}

int main(void)
/*@ trusted; @*/
{
    return check_sum(10 /*@ 3i32, 7i32 @*/);
}

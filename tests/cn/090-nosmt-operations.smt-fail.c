// Test: NoSMT multiplication is uninterpreted (should fail at SMT level)
// mul_uf(x, y) produces MulNoSMT which the solver treats as an uninterpreted
// function. The ensures clause asserts mul_uf(x, y) == x * y, but since
// mul_uf is opaque to the solver, it cannot prove this equality.

int identity(int x, int y)
/*@ requires x >= 0i32; x <= 100i32;
             y >= 0i32; y <= 100i32;
    ensures mul_uf(x, y) == x * y; @*/
{
    return 0;
}

int main(void)
/*@ trusted; @*/
{
    return identity(3, 7);
}

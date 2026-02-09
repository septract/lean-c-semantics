// Test: Return value uses multiple parameters
// Tests that parameter bindings work correctly with multiple params

int add(int a, int b)
/*@ requires a > 0i32; a < 500i32;
    requires b > 0i32; b < 500i32;
    ensures return == a + b; @*/
{
    return a + b;
}

int main(void)
{
    return add(20, 22);
}

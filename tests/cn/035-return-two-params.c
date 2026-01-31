// Test: Return value uses multiple parameters
// Tests that parameter bindings work correctly with multiple params

int add(int a, int b)
/*@ requires a > 0;
    requires b > 0;
    requires a + b < 1000;
    ensures return == a + b; @*/
{
    return a + b;
}

int main(void)
{
    return add(20, 22);
}

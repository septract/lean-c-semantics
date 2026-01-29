// Test: Return value is an expression
// Tests that return value substitution works with expressions

int increment(int x)
/*@ requires x < 1000;
    ensures return == x + 1; @*/
{
    return x + 1;
}

int main(void)
{
    return increment(41);
}

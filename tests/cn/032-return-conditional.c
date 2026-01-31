// Test: Return value depends on condition
// Tests that return value is correct in both branches

int abs_value(int x)
/*@ requires x > -1000;
    requires x < 1000;
    ensures return >= 0; @*/
{
    if (x >= 0) {
        return x;
    } else {
        return -x;
    }
}

int main(void)
{
    return abs_value(-5);
}

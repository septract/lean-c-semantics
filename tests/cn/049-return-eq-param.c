// Test: return equals parameter (no arithmetic in spec or body)
// Isolates: basic postcondition constraint with return == x
int identity(int x)
/*@ requires x >= 0;
    ensures return == x; @*/
{
    return x;
}

int main(void)
{
    return identity(42);
}

// Test: spec has x + 1 (addition with literal in spec only)
// Isolates: spec-side binop type resolution
// Body returns x + 1 but we're checking if the spec resolves properly
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

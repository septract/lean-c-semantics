// Test: Global variable with accesses clause
// Function reads a global variable declared via 'accesses'

int g;

int read_global(int x)
/*@ accesses g;
    requires x >= 0i32; x < 1000i32;
             g >= 0i32; g < 1000i32;
    ensures return == x + g; @*/
{
    return x + g;
}

int main(void)
/*@ trusted; @*/
{
    g = 5;
    return read_global(10);
}

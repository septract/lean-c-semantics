// Test: what's the first allocation address?
// Simplest possible test - just one local int
int main(void) {
    int a;
    long addr = (long)&a;
    return (int)(addr % 1000000);
}

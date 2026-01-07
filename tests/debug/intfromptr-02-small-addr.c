// Test: cast pointer with small address to int
// Expected: some value, no UB (address fits in int)
int x;
int main(void) {
    // Global at low address should fit in int
    long addr = (long)&x;
    // Cast to int - may or may not be UB depending on address
    return 0;
}

// Test: check actual address via long cast (no UB for long)
int main(void) {
    int a;
    // Cast to long first (should not trigger UB)
    long addr = (long)&a;
    // Return it (truncated to int for return value)
    // Use modulo to avoid overflow in return
    return (int)(addr % 1000000);
}

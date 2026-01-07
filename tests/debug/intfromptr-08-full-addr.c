// Test: check full address value
int main(void) {
    int a;
    long addr = (long)&a;
    // Print address in parts to avoid overflow
    int high = (int)(addr / 1000000000);
    int low = (int)(addr % 1000000000);
    // Return high part * 1000 + some indicator
    return high;  // If 0, address < 1 billion
}

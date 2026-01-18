// Test: char array address alignment
// Expected: B has alignment 1, so address may NOT be 8-byte aligned
// This tests that we match Cerberus memory layout

char B[32];

int main(void) {
    // Check if B's address is 8-byte aligned
    unsigned long addr = (unsigned long)&B;
    if (addr % 8 == 0) {
        return 1;  // aligned (8-byte)
    } else {
        return 0;  // not 8-byte aligned
    }
}

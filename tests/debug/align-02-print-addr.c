// Test: print actual addresses to debug alignment
char B[32];
int x;

int main(void) {
    // Return low bits of B's address
    unsigned long addr = (unsigned long)&B;
    return (int)(addr & 0xFF);  // Return low byte
}

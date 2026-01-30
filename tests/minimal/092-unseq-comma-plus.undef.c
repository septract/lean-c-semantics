// Comma sequences write, but plus makes read unsequenced - RACE (UB035)
// (x = 1, y) is evaluated, then + x is unsequenced with the write
int x, y;

int main(void) {
    (x = 1, y) + x;  // UB: write of x unsequenced with read of x
}

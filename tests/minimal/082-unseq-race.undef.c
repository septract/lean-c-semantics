// Unsequenced read and write to same location - RACE (UB035)
int x = 0;

int main(void) {
    // Left operand writes x, right operand reads x
    // These are unsequenced, causing a race
    return (x = 1) + x;  // UB: unsequenced race
}

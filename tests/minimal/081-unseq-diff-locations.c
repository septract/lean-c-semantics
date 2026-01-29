// Unsequenced writes to different locations - no race
int x = 0;
int y = 0;

int main(void) {
    // Both operands of + write, but to different locations
    return (x = 1) + (y = 2);  // Should return 3
}

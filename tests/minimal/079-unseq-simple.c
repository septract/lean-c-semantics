// Simple unsequenced expression - no race
// Binary + has unsequenced operands, but they only read, so no race
int main(void) {
    int x = 1;
    int y = 2;
    return x + y;  // Should return 3
}

// Unsequenced reads only - no race
// Both operands of + read x, but two reads never race
int x = 42;

int main(void) {
    return x + x;  // Should return 84
}

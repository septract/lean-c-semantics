// Pre-increment race - RACE (UB035)
// Both operands modify i, unsequenced
int i = 0;

int main(void) {
    ++i + ++i;  // UB: unsequenced race (two modifications)
}

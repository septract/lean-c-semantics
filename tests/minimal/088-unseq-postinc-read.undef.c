// Post-increment with unsequenced read - RACE (UB035)
// i++ modifies i, other operand reads i, unsequenced
int i = 0;

int main(void) {
    i++ + i;  // UB: unsequenced race (modification + read)
}

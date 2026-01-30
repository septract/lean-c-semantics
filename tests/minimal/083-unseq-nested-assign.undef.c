// Nested assignment to same location - RACE (UB035)
// The outer assignment and inner assignment are unsequenced
int x;

int main(void) {
    x = (x = 1);  // UB: unsequenced race
}

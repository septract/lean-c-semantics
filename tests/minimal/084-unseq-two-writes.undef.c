// Two unsequenced writes to same location - RACE (UB035)
int x;

int main(void) {
    (x = 1) + (x = 2);  // UB: unsequenced race (two writes)
}

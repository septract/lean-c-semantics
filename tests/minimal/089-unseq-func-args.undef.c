// Function arguments are unsequenced - RACE (UB035)
int x = 0;

int add(int a, int b) {
    return a + b;
}

int main(void) {
    return add(x = 1, x);  // UB: arguments unsequenced, write + read race
}

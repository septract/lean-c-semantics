// ctrl-007-loop-break-continue.c
// Loop using both break and continue: skip even numbers, break at 10.
// Exercises break/continue control flow in Cerberus reduction.

int main(void) {
    int sum = 0;

    for (int i = 0; i < 20; i++) {
        if (i == 10)
            break;
        if (i % 2 == 0)
            continue;
        sum = sum + i; // adds 1+3+5+7+9
    }

    return sum; // expected: 25
}

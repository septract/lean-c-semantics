// ctrl-009-for-empty-parts.c
// for(;;) with break, and for(init;;inc) with conditional break.
// Exercises for-loops with missing parts in Cerberus reduction.

int main(void) {
    int result = 0;

    // Infinite loop with break
    for (;;) {
        result = 5;
        break;
    }

    // Loop with no condition (only init and increment)
    int sum = 0;
    for (int i = 0; ; i++) {
        if (i >= 4)
            break;
        sum = sum + i; // adds 0+1+2+3
    }

    return result + sum; // expected: 5 + 6 = 11
}

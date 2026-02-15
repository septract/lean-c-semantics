// ctrl-005-goto-nested.c
// Goto that jumps out of a nested scope (inner block to outer label).
// Exercises scope-crossing goto in Cerberus reduction.

int main(void) {
    int result = 0;

    {
        int inner = 10;
        result = inner;
        if (inner == 10)
            goto done;
        result = 99; // skipped
    }

    result = 88; // skipped

done:
    return result; // expected: 10
}

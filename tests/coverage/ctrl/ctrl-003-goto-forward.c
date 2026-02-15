// ctrl-003-goto-forward.c
// Forward goto that skips over a variable assignment.
// Exercises goto/label control flow in Cerberus reduction.

int main(void) {
    int result = 1;

    goto skip;
    result = 99; // skipped
skip:
    result = result + 1;

    return result; // expected: 2
}

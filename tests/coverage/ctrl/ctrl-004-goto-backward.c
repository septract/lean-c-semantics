// ctrl-004-goto-backward.c
// Backward goto creating a manual loop that counts to 5.
// Exercises backward goto reduction in Cerberus.

int main(void) {
    int count = 0;

loop:
    count = count + 1;
    if (count < 5)
        goto loop;

    return count; // expected: 5
}

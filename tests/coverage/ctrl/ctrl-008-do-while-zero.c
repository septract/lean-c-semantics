// ctrl-008-do-while-zero.c
// do { ... } while(0) -- body executes exactly once.
// Exercises do-while with false condition in Cerberus reduction.

int main(void) {
    int count = 0;

    do {
        count = count + 1;
    } while (0);

    return count; // expected: 1
}

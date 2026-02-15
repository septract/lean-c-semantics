// expr-004-comma-complex.c
// Test comma operator in expressions and for-loop
// Exercises comma/sequence expression evaluation in core_eval.ml

int main(void) {
    // Comma operator evaluates left-to-right, returns last value
    int x = (1, 2, 3);  // x = 3

    // Comma in for-loop with multiple updates
    int sum = 0;
    for (int i = 0, j = 10; i < j; i++, j--) {
        sum += i;
    }
    // i=0,j=10 -> i=1,j=9 -> i=2,j=8 -> i=3,j=7 -> i=4,j=6 -> i=5,j=5 stop
    // sum = 0 + 1 + 2 + 3 + 4 = 10

    // x(3) + sum(10) = 13
    return x + sum - 13;
}

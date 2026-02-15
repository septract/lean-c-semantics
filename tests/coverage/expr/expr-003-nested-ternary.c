// expr-003-nested-ternary.c
// Test chained/nested ternary expressions
// Exercises conditional branching in core_eval.ml

int main(void) {
    int a = 1, b = 2, c = 3;

    // Nested ternary: right-associative a ? b : (c ? d : e)
    int r1 = a ? b : c ? 99 : 100;  // a is true, so r1 = b = 2

    int r2 = 0 ? 99 : c ? b : 100;  // 0 is false, c is true, so r2 = b = 2

    int r3 = 0 ? 99 : 0 ? 88 : 42;  // both false, r3 = 42

    // 2 + 2 + 42 = 46
    return r1 + r2 + r3 - 46;
}

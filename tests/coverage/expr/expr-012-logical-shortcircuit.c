// expr-012-logical-shortcircuit.c
// Test short-circuit evaluation with side effects
// Exercises PEnot / logical AND/OR short-circuit paths in core_eval.ml

int flag = 0;

int set_flag(void) {
    flag = 1;
    return 1;
}

int main(void) {
    // Short-circuit AND: 0 && f() should NOT call f()
    flag = 0;
    int r1 = 0 && set_flag();
    if (flag != 0) return 1;   // set_flag must not have been called
    if (r1 != 0) return 2;

    // Non-short-circuit AND: 1 && f() SHOULD call f()
    flag = 0;
    int r2 = 1 && set_flag();
    if (flag != 1) return 3;   // set_flag must have been called
    if (r2 != 1) return 4;

    // Short-circuit OR: 1 || f() should NOT call f()
    flag = 0;
    int r3 = 1 || set_flag();
    if (flag != 0) return 5;   // set_flag must not have been called
    if (r3 != 1) return 6;

    // Non-short-circuit OR: 0 || f() SHOULD call f()
    flag = 0;
    int r4 = 0 || set_flag();
    if (flag != 1) return 7;   // set_flag must have been called
    if (r4 != 1) return 8;

    // Nested short-circuit
    flag = 0;
    int r5 = (0 && set_flag()) || (1 && 1);
    if (flag != 0) return 9;   // set_flag not called (short-circuit in left &&)
    if (r5 != 1) return 10;

    return 0;
}

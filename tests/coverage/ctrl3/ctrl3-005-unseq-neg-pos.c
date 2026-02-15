// ctrl3-005-unseq-neg-pos.c
// Exercise do_race DA_neg vs DA_pos branch in core_reduction.ml (L253-258)
// An unsequenced expression where one operand writes and another reads
int main(void) {
    int x = 0;
    int y = 0;
    // x++ modifies x (neg action), y reads y (pos action)
    // The ordering in Eunseq matters for which branch is hit
    int r = (x++) + y; // may trigger neg-vs-pos check
    (void)r;
    // More explicit: write and read of SAME variable (definite race)
    int a = 1;
    int b = (a++) + a; // UB: unsequenced read and write of 'a'
    (void)b;
    return 0;
}

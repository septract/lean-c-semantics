// expr-009-negative-shift.c
// Test shift by negative amount (undefined behavior)
// Cerberus should detect this as UB
// Exercises PEop shift validation in core_eval.ml

int main(void) {
    int x = 1;
    int y = x << -1;  // UB: negative shift amount
    return y;
}

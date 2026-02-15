// expr-010-large-shift.c
// Test shift by amount >= bit width (undefined behavior)
// Cerberus should detect this as UB
// Exercises PEop shift bounds checking in core_eval.ml

int main(void) {
    int x = 1;
    int y = x << 32;  // UB: shift amount >= width of int (32)
    return y;
}

// Test: SeqRMW with strong sequencing (comma operator forces sseq)
// Exercises SeqRMW neg action path in core_reduction.ml
int main(void) {
    int x = 0;
    int y = (x++, x++);  // comma creates sseq, both are SeqRMW
    return y == 1 && x == 2 ? 0 : 1;
}

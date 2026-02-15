// ctrl3-004-falloff-nonvoid.c
// Exercise PEundef UB088_reached_end_of_function in core_eval.ml (L621)
// Falling off the end of a non-void function is UB
int no_return(int x) {
    if (x > 100) return x;
    // Fall through without return when x <= 100 (UB)
}
int main(void) {
    int result = no_return(50); // UB: fell off end
    (void)result;
    return 0;
}

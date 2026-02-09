// Test floating point overflow to Inf and NaN propagation
// IEEE 754: double overflow -> Inf, Inf - Inf -> NaN
// Float overflow is implementation-defined in C, not UB
int main(void) {
    // Overflow to Inf: 1e308 * 2.0 overflows double range
    double big = 1e308;
    double inf = big * 2.0;

    // NaN from Inf - Inf
    double nan = inf - inf;

    // Inf comparisons
    int r1 = (inf > 1e308);     // 1: Inf > any finite
    int r2 = (inf == inf);      // 1: Inf == Inf (IEEE 754)

    // NaN comparisons - all comparisons with NaN are false (IEEE 754)
    int r3 = (nan == nan);      // 0: NaN != NaN
    int r4 = (nan == 0.0);      // 0
    int r5 = (nan < 1.0);       // 0

    // Arithmetic with Inf
    double y = inf + 1.0;
    int r6 = (y == inf);        // 1: Inf + finite = Inf

    // Float to int conversion of finite value
    double c = 3.14 + 2.0;      // 5.14
    int r7 = (int)c;            // 5: truncation

    // Expected: 1 + 1 + 0 + 0 + 0 + 1 + 5 = 8
    return r1 + r2 + r3 + r4 + r5 + r6 + r7;
}

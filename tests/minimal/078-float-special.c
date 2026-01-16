// Test: IEEE 754 special float values (Infinity)
// Tests storing and loading Infinity values via bit manipulation

int main(void) {
    // Create +Infinity via union (IEEE 754: 0x7FF0000000000000)
    union { double d; unsigned long long u; } pos_inf;
    pos_inf.u = 0x7FF0000000000000ULL;

    // Create -Infinity via union (IEEE 754: 0xFFF0000000000000)
    union { double d; unsigned long long u; } neg_inf;
    neg_inf.u = 0xFFF0000000000000ULL;

    // Store to memory and load back
    volatile double v_pos = pos_inf.d;
    volatile double v_neg = neg_inf.d;

    // Infinity comparisons work as expected
    int result = 0;
    if (v_pos > 1e308) result += 1;      // +Inf is greater than any finite
    if (v_neg < -1e308) result += 2;     // -Inf is less than any finite
    if (v_pos == v_pos) result += 4;     // Inf equals itself

    return result;  // Expected: 7
}

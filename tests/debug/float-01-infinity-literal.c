// Test: IEEE 754 Infinity from literal overflow
// 1e309 overflows double range, becomes Infinity
// This exercises the memValueToBytes .posInf codepath

int main(void) {
    volatile double inf = 1e309;  // Overflows to +Infinity
    volatile double neg_inf = -1e309;  // Overflows to -Infinity

    int result = 0;
    if (inf > 1e308) result += 1;      // +Inf > any finite
    if (neg_inf < -1e308) result += 2; // -Inf < any finite

    return result;  // Expected: 3
}

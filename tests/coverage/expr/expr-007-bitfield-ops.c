// expr-007-bitfield-ops.c
// Test bitfield struct: read, write, arithmetic
// Exercises bitfield member access paths in core_eval.ml

struct flags {
    unsigned int a : 3;   // 0-7
    unsigned int b : 5;   // 0-31
    unsigned int c : 1;   // 0-1
};

int main(void) {
    struct flags f;
    f.a = 5;    // 101 in binary
    f.b = 20;   // 10100 in binary
    f.c = 1;

    // Read back
    if (f.a != 5) return 1;
    if (f.b != 20) return 2;
    if (f.c != 1) return 3;

    // Arithmetic on bitfields
    int sum = f.a + f.b + f.c;  // 5 + 20 + 1 = 26
    if (sum != 26) return 4;

    // Overflow: 3-bit field wraps at 8
    f.a = 7;
    f.a = f.a + 1;  // wraps: 8 & 0x7 = 0
    if (f.a != 0) return 5;

    return 0;
}

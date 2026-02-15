// expr-008-enum-arith.c
// Test arithmetic on enum values
// Exercises enum constant evaluation in core_eval.ml

enum color { RED = 1, GREEN = 2, BLUE = 4 };
enum sequential { A = 0, B, C, D };  // B=1, C=2, D=3

int main(void) {
    enum color c = RED;

    // Enum arithmetic
    int sum = RED + GREEN + BLUE;  // 1 + 2 + 4 = 7
    if (sum != 7) return 1;

    // Bitwise on enum values
    int mask = RED | GREEN | BLUE;  // 0b111 = 7
    if (mask != 7) return 2;

    // Sequential enum
    int seq = A + B + C + D;  // 0 + 1 + 2 + 3 = 6
    if (seq != 6) return 3;

    // Enum in comparison
    if (RED >= GREEN) return 4;
    if (BLUE <= GREEN) return 5;

    // Enum in ternary
    int r = (c == RED) ? 42 : 99;
    if (r != 42) return 6;

    return 0;
}

// expr-011-sequence-point.c
// Test well-ordered complex expressions with multiple operations
// Avoids actual unsequenced UB; uses properly sequenced updates
// Exercises expression evaluation ordering in core_eval.ml

int main(void) {
    // Pre-increment is well-defined when sequenced
    int a = 1;
    int b = ++a;       // a becomes 2, b = 2
    int c = a + b;     // c = 2 + 2 = 4

    if (a != 2) return 1;
    if (b != 2) return 2;
    if (c != 4) return 3;

    // Compound assignment chains (each is a full expression)
    int x = 10;
    x += 5;    // x = 15
    x *= 2;    // x = 30
    x -= 3;    // x = 27

    if (x != 27) return 4;

    // Logical operators provide sequence points
    int d = 0;
    int e = (d = 1) && (d = d + 1);  // d=1 (true), then d=2 (true), e=1
    if (d != 2) return 5;
    if (e != 1) return 6;

    // Comma operator provides sequence point
    int f = (a = 10, a + 5);  // a=10, then f = 15
    if (f != 15) return 7;

    return 0;
}

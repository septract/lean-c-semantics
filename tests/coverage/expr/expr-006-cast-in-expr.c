// expr-006-cast-in-expr.c
// Test casts as subexpressions
// Exercises PEop cast/conversion paths in core_eval.ml

int main(void) {
    // Float to int truncation
    int a = (int)3.7;          // a = 3

    // Narrowing cast: 256 wraps to 0 in char (unsigned char)
    unsigned char b = (unsigned char)256;  // b = 0

    // Int to unsigned
    unsigned int c = (unsigned int)(-1);   // c = UINT_MAX

    // Double arithmetic with cast
    int d = (int)(2.5 + 1.5);  // d = 4

    // Chained casts
    int e = (int)(char)(short)65;  // e = 65 ('A')

    // a(3) + b(0) + d(4) + e(65) = 72
    // c is huge, check it separately
    if (a != 3) return 1;
    if (b != 0) return 2;
    if (c != (unsigned int)(-1)) return 3;
    if (d != 4) return 4;
    if (e != 65) return 5;

    return 0;
}

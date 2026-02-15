// struct-009-init-partial.c
// Partial struct initialization. Uninitialized fields must be zero.
// Exercises: PEstruct with partial initializer list, zero-fill semantics.

struct S {
    int a;
    int b;
    int c;
    int d;
};

int main(void) {
    struct S s = {1, 2};
    // s.a == 1, s.b == 2, s.c == 0, s.d == 0

    int sum = s.a + s.b + s.c + s.d;
    // 1 + 2 + 0 + 0 = 3
    return sum;
}

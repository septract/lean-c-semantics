// struct-006-struct-return.c
// Function that returns a struct by value.
// Exercises: PEstruct in return position, struct return ABI.

struct S {
    int a;
    int b;
};

struct S make(int x, int y) {
    struct S s;
    s.a = x;
    s.b = y;
    return s;
}

int main(void) {
    struct S r = make(7, 8);
    int sum = r.a + r.b;
    // 7 + 8 = 15
    return sum;
}

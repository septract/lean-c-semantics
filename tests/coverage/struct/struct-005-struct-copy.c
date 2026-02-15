// struct-005-struct-copy.c
// Struct assignment (bulk copy).
// Exercises: PEstruct construction and struct-to-struct assignment.

struct S {
    int a;
    int b;
};

int main(void) {
    struct S x;
    x.a = 10;
    x.b = 20;

    struct S y = x;

    int sum = y.a + y.b;
    // 10 + 20 = 30
    return sum;
}

// struct-001-nested-struct.c
// Struct containing another struct. Access inner fields.
// Exercises: PEstruct construction and PEmemberof on nested struct types.

struct Inner {
    int a;
    int b;
};

struct Outer {
    struct Inner inner;
    int c;
};

int main(void) {
    struct Outer o;
    o.inner.a = 10;
    o.inner.b = 20;
    o.c = 30;

    int sum = o.inner.a + o.inner.b + o.c;
    // 10 + 20 + 30 = 60
    return sum;
}

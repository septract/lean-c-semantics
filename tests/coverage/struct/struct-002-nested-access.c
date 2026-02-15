// struct-002-nested-access.c
// Three levels of nested struct access: s.mid.inner.val
// Exercises: chained PEmemberof on deeply nested structs.

struct Level3 {
    int val;
};

struct Level2 {
    struct Level3 inner;
};

struct Level1 {
    struct Level2 mid;
};

int main(void) {
    struct Level1 s;
    s.mid.inner.val = 42;

    int r = s.mid.inner.val;
    return r;
}

// struct-008-anon-struct.c
// Anonymous struct member, accessed directly from outer struct.
// Exercises: PEmemberof with anonymous struct flattening.

struct S {
    struct {
        int x;
        int y;
    };
    int z;
};

int main(void) {
    struct S s;
    s.x = 3;
    s.y = 4;
    s.z = 5;

    int sum = s.x + s.y + s.z;
    // 3 + 4 + 5 = 12
    return sum;
}

// struct-010-union-in-struct.c
// Struct containing a union member. Access union through struct.
// Exercises: PEstruct + PEunion combined, PEmemberof on mixed struct/union.

union Value {
    int i;
    unsigned int u;
};

struct Tagged {
    int tag;
    union Value val;
};

int main(void) {
    struct Tagged t;
    t.tag = 1;
    t.val.i = 55;

    int result = t.tag + t.val.i;
    // 1 + 55 = 56
    return result;
}

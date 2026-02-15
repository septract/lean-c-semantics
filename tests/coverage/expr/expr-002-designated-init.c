// expr-002-designated-init.c
// Test designated initializers in struct initialization
// Exercises PEctor with designated field paths in core_eval.ml

struct point {
    int x;
    int y;
    int z;
};

int main(void) {
    struct point p = {.z = 30, .x = 10, .y = 20};
    // 10 + 20 + 30 = 60
    return p.x + p.y + p.z - 60;
}

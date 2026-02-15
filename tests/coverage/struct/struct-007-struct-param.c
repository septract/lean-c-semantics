// struct-007-struct-param.c
// Pass a struct by value to a function.
// Exercises: PEstruct as function argument, struct copy on call.

struct Point {
    int x;
    int y;
};

int sum_point(struct Point p) {
    return p.x + p.y;
}

int main(void) {
    struct Point pt;
    pt.x = 13;
    pt.y = 29;

    int result = sum_point(pt);
    // 13 + 29 = 42
    return result;
}

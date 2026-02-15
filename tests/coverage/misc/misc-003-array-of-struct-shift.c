// Test: array of structs exercises array_shift + member_shift paths
// Exercises: array_shift_ptrval for indexing and member_shift_ptrval
//            for field access on struct arrays.
struct Point { int x; int y; };
int main(void) {
    struct Point pts[3] = {{1, 2}, {3, 4}, {5, 6}};
    struct Point *p = pts;
    int sum = p[0].x + p[1].y + p[2].x;
    return sum == 1 + 4 + 5 ? 0 : 1;
}

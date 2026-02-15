// misc-011-member-shift-ptr.c
// Exercise PtrMemberShift memop in driver.ml (L776-781)
// Access struct members through pointer (p->member)
struct Point { int x; int y; int z; };
void init(struct Point *p, int a, int b, int c) {
    p->x = a;
    p->y = b;
    p->z = c;
}
int sum(struct Point *p) {
    return p->x + p->y + p->z;
}
int main(void) {
    struct Point pt;
    init(&pt, 10, 20, 12);
    if (sum(&pt) != 42) return 1;
    return 0;
}

// union3-005-union-return.c
// Exercise union value return (passes union as value)
union U { int i; char c; };
union U make_union(int val) {
    union U u;
    u.i = val;
    return u;
}
int main(void) {
    union U u = make_union(77);
    if (u.i != 77) return 1;
    return 0;
}

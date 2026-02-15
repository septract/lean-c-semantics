// union3-006-union-memberof.c
// Exercise PEmemberof union path in core_eval.ml (L955-975)
// Access member of union value, not through pointer
union U { int x; int y; };
union U get(void) {
    union U u;
    u.x = 99;
    return u;
}
int main(void) {
    // Access member of returned union value directly
    int val = get().x;
    if (val != 99) return 1;
    return 0;
}

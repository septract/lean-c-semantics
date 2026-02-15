// union3-007-nested-union.c
// Exercise nested union/struct repr/abst paths
struct Inner { int a; int b; };
union Outer { struct Inner s; long l; };
int main(void) {
    union Outer o;
    o.s.a = 10;
    o.s.b = 20;
    if (o.s.a != 10) return 1;
    if (o.s.b != 20) return 2;
    // Now write via the other member
    o.l = 0;
    return 0;
}

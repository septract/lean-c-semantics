// union3-004-union-copy.c
// Exercise union assignment (bulk memory copy of union)
union U { int i; char c[8]; };
int main(void) {
    union U a;
    a.i = 12345;
    union U b = a; // union copy
    if (b.i != 12345) return 1;
    union U c;
    c = a; // union assignment
    if (c.i != 12345) return 2;
    return 0;
}

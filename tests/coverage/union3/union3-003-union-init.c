// union3-003-union-init.c
// Exercise AilEunion translation path
union U { int i; char c; double d; };
int main(void) {
    union U u1 = { .i = 100 };
    if (u1.i != 100) return 1;
    union U u2 = { .c = 'A' };
    if (u2.c != 'A') return 2;
    return 0;
}

// misc-004-void-return.c
// Exercise AilSreturnVoid in translation.ml (L3948-3966)
// Explicit return; in void function (not just falling off the end)
void foo(int *p) {
    *p = 42;
    return;
}
void bar(int *p, int cond) {
    if (cond) {
        *p = 10;
        return;
    }
    *p = 20;
    return;
}
int main(void) {
    int x = 0;
    foo(&x);
    if (x != 42) return 1;
    bar(&x, 1);
    if (x != 10) return 2;
    bar(&x, 0);
    if (x != 20) return 3;
    return 0;
}

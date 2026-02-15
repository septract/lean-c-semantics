// mem3-005-struct-multi-ptr.c
// Exercise merge_taint NewTaint cases in impl_mem.ml (L932-939)
// Struct containing multiple pointers exercises taint merging on load
struct TwoPtr { int *p; int *q; };
int main(void) {
    int a = 10, b = 20;
    struct TwoPtr s;
    s.p = &a;
    s.q = &b;
    // Loading the struct back merges taint from both pointer members
    struct TwoPtr t = s;
    if (*t.p != 10) return 1;
    if (*t.q != 20) return 2;
    return 0;
}

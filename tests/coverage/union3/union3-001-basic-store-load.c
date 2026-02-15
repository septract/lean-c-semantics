// union3-001-basic-store-load.c
// Exercise MVunion repr/abst in impl_mem.ml, PEunion in core_eval.ml
union U { int i; float f; };
int main(void) {
    union U u;
    u.i = 42;
    if (u.i != 42) return 1;
    return 0;
}

// ptr-006-void-ptr-cast.c
// Cast to and from void*.
// Exercises: impl_mem.ml pointer cast to/from void*
// Expected: exit 0
int main(void) {
    int x = 42;
    void *v = &x;
    int *p = v;
    return *p == 42 ? 0 : 1;
}

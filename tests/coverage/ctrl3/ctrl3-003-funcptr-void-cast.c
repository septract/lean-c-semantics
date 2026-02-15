// ctrl3-003-funcptr-void-cast.c
// Exercise PEcfunction case_funsym_opt path in core_eval.ml (L919-926)
// Cast function pointer through void* and call
int add(int a, int b) { return a + b; }
int main(void) {
    int (*fp)(int, int) = &add;
    void *p = (void*)fp;           // function pointer to void*
    int (*fp2)(int, int) = (int (*)(int, int))p;  // void* back to function pointer
    int result = fp2(20, 22);      // call through recovered function pointer
    if (result != 42) return 1;
    return 0;
}

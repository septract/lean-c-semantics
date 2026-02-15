// ctrl3-002-null-funcptr-call.c
// Exercise null function pointer call path in core_reduction.ml (L1407)
// This is UB but exercises the error detection path
typedef void (*func_t)(void);
int main(void) {
    func_t fp = (func_t)0; // null function pointer
    fp(); // UB: calling null function pointer
    return 0;
}

// arith3-003-unsigned-shl.c
// Exercise IOpShl in core_eval.ml mk_iop (L91)
int main(void) {
    unsigned int x = 1u;
    unsigned int y = x << 16u;  // IOpShl
    if (y != 65536u) return 1;
    unsigned int z = 0xFFu << 8u;
    if (z != 0xFF00u) return 2;
    return 0;
}

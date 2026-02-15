// arith3-004-unsigned-shr.c
// Exercise IOpShr in core_eval.ml mk_iop (L92)
int main(void) {
    unsigned int x = 0xFFFF0000u;
    unsigned int y = x >> 16u;  // IOpShr
    if (y != 0xFFFFu) return 1;
    unsigned int z = 256u >> 4u;
    if (z != 16u) return 2;
    return 0;
}

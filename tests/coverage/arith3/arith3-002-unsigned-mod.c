// arith3-002-unsigned-mod.c
// Exercise IOpRem_t in core_eval.ml mk_iop (L90)
int main(void) {
    unsigned int x = 100u;
    unsigned int y = x % 7u;  // IOpRem_t
    if (y != 2u) return 1;
    unsigned int z = 42u % 42u;
    if (z != 0u) return 2;
    return 0;
}

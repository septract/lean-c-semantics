// arith3-001-unsigned-div.c
// Exercise IOpDiv in core_eval.ml mk_iop (L89) via PEwrapI
// Unsigned division goes through the wrapping integer op path
int main(void) {
    unsigned int x = 100u;
    unsigned int y = x / 3u;  // IOpDiv
    if (y != 33u) return 1;
    unsigned int z = 0u / 1u; // division with zero dividend
    if (z != 0u) return 2;
    return 0;
}

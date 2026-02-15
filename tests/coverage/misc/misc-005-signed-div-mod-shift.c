// misc-005-signed-div-mod-shift.c
// Exercise IOpDiv, IOpRem_t, IOpShl, IOpShr in core_eval.ml (L89-92)
// Signed integer division, remainder, and shifts
int main(void) {
    int a = 17;
    int b = 5;
    int div = a / b;    // IOpDiv -> 3
    if (div != 3) return 1;
    int rem = a % b;    // IOpRem_t -> 2
    if (rem != 2) return 2;
    int shl = a << 2;   // IOpShl -> 68
    if (shl != 68) return 3;
    int shr = a >> 2;   // IOpShr -> 4
    if (shr != 4) return 4;
    // Negative division
    int ndiv = -17 / 5; // -> -3
    if (ndiv != -3) return 5;
    int nrem = -17 % 5; // -> -2
    if (nrem != -2) return 6;
    return 0;
}

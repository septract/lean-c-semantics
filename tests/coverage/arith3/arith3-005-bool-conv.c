// arith3-005-bool-conv.c
// Exercise mk_conv_int _Bool path in core_eval.ml (L65,69)
// Converting integers to _Bool: 0 -> false (0), nonzero -> true (1)
int main(void) {
    _Bool b1 = (_Bool)0;
    if (b1 != 0) return 1;
    _Bool b2 = (_Bool)1;
    if (b2 != 1) return 2;
    _Bool b3 = (_Bool)42;   // nonzero -> 1
    if (b3 != 1) return 3;
    _Bool b4 = (_Bool)-1;   // nonzero -> 1
    if (b4 != 1) return 4;
    int x = 100;
    _Bool b5 = x;           // implicit conversion
    if (b5 != 1) return 5;
    return 0;
}

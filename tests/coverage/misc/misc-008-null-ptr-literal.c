// misc-008-null-ptr-literal.c
// Exercise ConstantNull in translation.ml (L199-200)
// Use null pointer constant in pointer context
int main(void) {
    int *p = 0;           // ConstantNull
    if (p != 0) return 1; // compare with null
    char *q = 0;          // ConstantNull with different type
    if (q != 0) return 2;
    return 0;
}

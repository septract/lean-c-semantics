// expr-001-compound-literal.c
// Test compound literal expression: (int[]){1,2,3}
// Exercises PEctor / compound literal code paths in core_eval.ml

int main(void) {
    int *p = (int[]){10, 20, 30};
    int a = p[0];
    int b = p[1];
    int c = p[2];
    // 10 + 20 + 30 = 60
    return a + b + c - 60;
}

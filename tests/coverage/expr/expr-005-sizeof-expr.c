// expr-005-sizeof-expr.c
// Test sizeof on various types and expressions
// Exercises PEop/sizeof evaluation in core_eval.ml

struct pair {
    int a;
    int b;
};

int main(void) {
    int arr[10];

    int s1 = sizeof(char);           // 1
    int s2 = sizeof(int);            // typically 4
    int s3 = sizeof(arr);            // typically 40 (10 * 4)
    int s4 = sizeof(struct pair);    // typically 8 (2 * 4)
    int s5 = sizeof(arr[0]);         // same as sizeof(int), typically 4

    // Verify relative sizes rather than absolute (portable)
    // sizeof(char) must be 1
    if (s1 != 1) return 1;
    // sizeof(int) must be >= sizeof(char)
    if (s2 < s1) return 2;
    // sizeof(arr) must be 10 * sizeof(int)
    if (s3 != 10 * s2) return 3;
    // sizeof(struct pair) must be >= 2 * sizeof(int)
    if (s4 < 2 * s2) return 4;
    // sizeof(arr[0]) must equal sizeof(int)
    if (s5 != s2) return 5;

    return 0;
}

// Test: exit() called before out-of-bounds access would happen
// Expected: clean exit (no UB) - THIS IS THE pr55875 PATTERN
void exit(int);
int a[10];
int f(int x) {
    if (x == 0) exit(0);
    return 0;
}
int main(void) {
    // C semantics: a[10] lvalue and f(0) are unsequenced
    // With left-to-right sequentialization, a[10] is evaluated first
    // Question: does evaluating &a[10] for store trigger UB?
    a[10] = f(0);
    return 1;  // should never reach
}

// ptr2-015-funcptr-param.c
// Pass a function pointer as a parameter and call it.
// Exercises PEcfunction and function pointer argument passing.
// Expected return: 42
int apply(int (*f)(int), int x) { return f(x); }
int dbl(int x) { return x * 2; }

int main(void) {
    return apply(dbl, 21);
}

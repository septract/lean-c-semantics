// ctrl-012-multi-decl.c
// Multiple declarations in one statement: int a=1, b=2, c=3;
// Exercises multiple Elet bindings from a single declaration.

int main(void) {
    int a = 1, b = 2, c = 3;
    int x = a + b, y = x + c;

    return y; // expected: (1+2) + 3 = 6
}

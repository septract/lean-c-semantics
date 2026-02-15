// ctrl-011-nested-scope-vars.c
// Nested blocks with same-named variables in different scopes.
// Exercises Elet with shadowed bindings in core_reduction.ml.

int main(void) {
    int result = 0;
    int x = 1;

    result = result + x; // x=1

    {
        int x = 2;
        result = result + x; // x=2
        {
            int x = 3;
            result = result + x; // x=3
        }
        result = result + x; // x=2
    }

    result = result + x; // x=1

    return result; // expected: 1+2+3+2+1 = 9
}

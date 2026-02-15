// ctrl-006-nested-if-deep.c
// 6 levels of nested if-else.
// Exercises deep Eif nesting in core_reduction.ml.

int main(void) {
    int a = 1, b = 2, c = 3, d = 4, e = 5, f = 6;
    int result = 0;

    if (a == 1) {
        if (b == 2) {
            if (c == 3) {
                if (d == 4) {
                    if (e == 5) {
                        if (f == 6) {
                            result = 42;
                        } else {
                            result = 1;
                        }
                    } else {
                        result = 2;
                    }
                } else {
                    result = 3;
                }
            } else {
                result = 4;
            }
        } else {
            result = 5;
        }
    } else {
        result = 6;
    }

    return result; // expected: 42
}

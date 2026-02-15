// ctrl-001-nested-switch.c
// Switch inside switch: outer on x, inner on y.
// Exercises nested Ecase reduction in core_reduction.ml.

int main(void) {
    int x = 2;
    int y = 1;
    int result = 0;

    switch (x) {
    case 1:
        result = 10;
        break;
    case 2:
        switch (y) {
        case 0:
            result = 20;
            break;
        case 1:
            result = 21;
            break;
        default:
            result = 29;
            break;
        }
        break;
    case 3:
        result = 30;
        break;
    default:
        result = 99;
        break;
    }

    return result; // expected: 21
}

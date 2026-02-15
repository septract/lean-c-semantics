// ctrl-002-switch-many-cases.c
// Switch with 12 cases and a default.
// Exercises Ecase with many branches in core_reduction.ml.

int main(void) {
    int x = 7;
    int result;

    switch (x) {
    case 0:  result = 100; break;
    case 1:  result = 101; break;
    case 2:  result = 102; break;
    case 3:  result = 103; break;
    case 4:  result = 104; break;
    case 5:  result = 105; break;
    case 6:  result = 106; break;
    case 7:  result = 107; break;
    case 8:  result = 108; break;
    case 9:  result = 109; break;
    case 10: result = 110; break;
    case 11: result = 111; break;
    default: result = 999; break;
    }

    return result; // expected: 107
}

// Reduced from 20021118-2.c - multiple float params
#include <stdlib.h>

void f2(double f1, double f2) {
    if (f1 != 2.5 || f2 != 3.5)
        abort();
}

int main(void) {
    f2(2.5, 3.5);
    return 0;
}

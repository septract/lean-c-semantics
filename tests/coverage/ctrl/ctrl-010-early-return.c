// ctrl-010-early-return.c
// Function with multiple return paths based on conditionals.
// Exercises early return reduction in Cerberus.

int classify(int n) {
    if (n < 0)
        return -1;
    if (n == 0)
        return 0;
    if (n < 10)
        return 1;
    if (n < 100)
        return 2;
    return 3;
}

int main(void) {
    int a = classify(-5);   // -1
    int b = classify(0);    //  0
    int c = classify(7);    //  1
    int d = classify(50);   //  2
    int e = classify(200);  //  3

    return a + 1 + b + c + d + e; // expected: (-1+1) + 0 + 1 + 2 + 3 = 6
}

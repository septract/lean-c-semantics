// ptr2-014-funcptr-array.c
// Array of function pointers, invoke each and sum results.
// Exercises function pointer loads and indirect calls.
// Expected return: 6 (1+2+3)
int f1(void) { return 1; }
int f2(void) { return 2; }
int f3(void) { return 3; }

int main(void) {
    int (*fps[3])(void) = {f1, f2, f3};
    return fps[0]() + fps[1]() + fps[2]();
}

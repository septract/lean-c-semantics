// ptr2-013-funcptr-call.c
// Call through a function pointer.
// Exercises PEcfunction (0% covered) for indirect calls.
// Expected return: 7
int add(int a, int b) { return a + b; }

int main(void) {
    int (*fp)(int, int) = &add;
    return fp(3, 4);
}

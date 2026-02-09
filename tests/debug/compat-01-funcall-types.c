// Test are_compatible: function call with matching types
// The translation generates PEare_compatible to check argument compatibility
// at function call sites (C11 6.5.2.2#9)
int add(int a, int b) {
    return a + b;
}

int main(void) {
    int x = 10;
    int y = 20;
    int result = add(x, y);
    return result;  // Expected: 30
}

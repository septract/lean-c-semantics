// Test: cast local variable address to int
// This is the function_vs_var pattern
// Expected: UB024 if address doesn't fit in signed int range
int main(void) {
    int a;
    return (int)&a;
}

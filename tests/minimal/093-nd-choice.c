// Test that nd (End) expressions are handled correctly
// This tests nondeterministic choice in exhaustive mode
// Cerberus generates End expressions for boolean coercion
int main(void) {
    if (1)
        return 42;
    else
        return 0;
}

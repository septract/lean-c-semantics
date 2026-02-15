// Test: string literal indexing (exercises store_lock + load)
int main(void) {
    const char *s = "ABCDE";
    int sum = s[0] + s[1] + s[2] + s[3] + s[4];
    // A=65, B=66, C=67, D=68, E=69, sum=335
    return sum == 335 ? 0 : 1;
}

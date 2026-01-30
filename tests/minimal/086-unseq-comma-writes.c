// Multiple writes sequenced by comma - NO RACE
// Each write is sequenced after the previous by comma operator
int x;

int main(void) {
    (x = 0, x = 1, x = 2);  // No race: all writes sequenced
    return x;  // Should return 2
}

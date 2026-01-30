// Comma operator sequences operations - NO RACE
// Read of x is sequenced before write by comma operator
int x = 42;

int main(void) {
    (x, x = 0);  // No race: read sequenced before write
    return 0;
}

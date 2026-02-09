// Test: enum type argument to function expecting int
// Cerberus normalizes enum values at call sites, so are_compatible
// sees signed int == signed int (structural equality works)
enum color { RED = 0, GREEN = 1, BLUE = 2 };

int get_value(int x) {
    return x + 10;
}

int main(void) {
    enum color c = GREEN;
    return get_value(c);  // Expected: 11
}

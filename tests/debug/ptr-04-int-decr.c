// Test integer decrement (to verify seq_rmw works for ints)
int main(void) {
    int x = 10;
    x--;
    return x;  // should return 9
}

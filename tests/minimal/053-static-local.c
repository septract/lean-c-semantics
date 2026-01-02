// Minimal: static local variable
// Tests that the variable retains value across calls
int counter(void) {
  static int count = 0;
  count++;
  return count;
}

int main(void) {
  counter();
  return counter(); // Should be 2
}

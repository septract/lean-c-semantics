// Minimal: comma operator
int main(void) {
  int x;
  // Comma operator evaluates both operands and returns the second
  x = (10, 20);
  return x;  // 20
}

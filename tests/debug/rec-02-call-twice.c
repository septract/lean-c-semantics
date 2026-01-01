// Call function twice
int f(int n) {
  return n;
}

int main(void) {
  int a = f(3);
  int b = f(2);
  return a + b;  // Expected: 5
}

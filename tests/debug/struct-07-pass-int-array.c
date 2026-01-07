// Test: passing array directly (decays to pointer)
int foo(int *arr) {
  return arr[0] + arr[1];
}

int main() {
  int f[2] = { 10, 20 };
  return foo(f);
}

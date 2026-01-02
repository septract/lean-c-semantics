// Minimal: function pointer
int add(int a, int b) {
  return a + b;
}

int main(void) {
  int (*func_ptr)(int, int) = add;
  return func_ptr(10, 20); // 30
}

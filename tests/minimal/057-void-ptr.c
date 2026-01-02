// Minimal: void pointer cast
int main(void) {
  int x = 42;
  void *p = &x;
  // Cast back and dereference
  return *(int*)p; // 42
}

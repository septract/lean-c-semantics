// Minimal: null pointer dereference (undefined behavior)
int main(void) {
  int *p = 0;
  return *p;  // UB: null pointer dereference
}

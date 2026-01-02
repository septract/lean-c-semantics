// Minimal: pointer to pointer
int main(void) {
  int x = 42;
  int *p = &x;
  int **pp = &p;
  return **pp;  // 42
}

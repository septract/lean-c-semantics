// Minimal: write through pointer
int main(void) {
  int x = 5;
  int *p = &x;
  *p = 20;
  return x;  // 20
}

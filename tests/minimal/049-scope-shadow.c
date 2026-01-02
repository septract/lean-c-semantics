// Minimal: variable shadowing
int main(void) {
  int x = 10;
  {
    int x = 20;
    if (x != 20) return 1;
  }
  return x; // 10
}

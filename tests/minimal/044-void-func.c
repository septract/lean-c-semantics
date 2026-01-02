// Minimal: void function with side effect
int g = 0;

void inc_global(void) {
  g++;
}

int main(void) {
  inc_global();
  inc_global();
  return g;  // 2
}

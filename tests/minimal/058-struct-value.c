// Minimal: struct pass-by-value
struct Data {
  int x;
};

void modify(struct Data d) {
  d.x = 99; // Should modify copy, not original
}

int main(void) {
  struct Data d = {42};
  modify(d);
  return d.x; // 42
}

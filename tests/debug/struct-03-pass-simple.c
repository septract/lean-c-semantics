struct s { int x; int y; };

int foo(struct s s) {
  return s.x + s.y;
}

int main() {
  struct s s = { 10, 20 };
  return foo(s);
}

struct s { int f[2]; };

int foo(struct s s) {
  return s.f[0] + s.f[1];
}

int main() {
  struct s s = { 10, 20 };
  return foo(s);
}

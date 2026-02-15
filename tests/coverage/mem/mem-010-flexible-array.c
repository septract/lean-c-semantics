// Test: struct with flexible array member
// Exercises: impl_mem.ml flexible array member sizeof and type handling
struct flex {
  int n;
  int data[];
};

int main(void) {
  // sizeof should be the size of just the fixed members (no FAM contribution)
  int sz = sizeof(struct flex);
  // sz should equal sizeof(int), possibly with padding
  return (sz >= (int)sizeof(int)) ? 0 : 1;
}

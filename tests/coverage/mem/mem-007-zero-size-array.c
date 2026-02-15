// Test: zero-size allocation edge case
// Exercises: impl_mem.ml allocation size edge cases
// Use sizeof on a struct with only a flexible array member to get minimal size
struct empty_like {
  char a[0];
};

int main(void) {
  int s = sizeof(struct empty_like);
  return (s == 0) ? 0 : 1;
}

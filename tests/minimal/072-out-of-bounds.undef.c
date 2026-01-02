// Minimal: array out of bounds (undefined behavior)
int main(void) {
  int arr[3] = {1, 2, 3};
  return arr[10];  // UB: out of bounds access
}

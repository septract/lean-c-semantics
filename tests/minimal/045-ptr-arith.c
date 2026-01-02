// Minimal: pointer arithmetic
int main(void) {
  int arr[3] = {10, 20, 30};
  int *p = arr;
  p++;
  return *p;  // 20
}

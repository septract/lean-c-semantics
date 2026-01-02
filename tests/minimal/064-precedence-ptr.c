// Minimal: operator precedence (*p++)
int main(void) {
  int arr[] = {10, 20};
  int *p = arr;
  // returns *p (10), then increments p
  int val = *p++; 
  return val + *p; // 10 + 20 = 30
}

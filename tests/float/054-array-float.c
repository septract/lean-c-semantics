// Test: float array store/load
int main(void) {
  float arr[3] = {1.0f, 2.0f, 3.0f};
  float sum = arr[0] + arr[1] + arr[2];
  return (sum == 6.0f) ? 0 : 1;
}

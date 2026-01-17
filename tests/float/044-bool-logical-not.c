// Test: logical NOT on float (this was the original bug trigger)
int main(void) {
  float a = 1.0f;
  int result = !a;  // Should be 0 (false)
  return result;
}

// Test: float returned from function
float get_pi(void) {
  return 3.14159f;
}

int main(void) {
  float p = get_pi();
  return (p == 3.14159f) ? 0 : 1;
}

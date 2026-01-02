// Minimal: char array initialization from string
int main(void) {
  char s[] = "ABC";
  // Verify it's a copy on the stack we can modify
  s[0] = 'Z'; 
  return s[0]; // 'Z' (90)
}

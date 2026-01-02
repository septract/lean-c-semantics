// Minimal: sizeof type
// Note: Assumes int is at least 2 bytes, but usually 4. 
// We return 1 to indicate success if it's > 0.
int main(void) {
  if (sizeof(int) > 0 && sizeof(char) == 1) {
    return 1;
  }
  return 0;
}

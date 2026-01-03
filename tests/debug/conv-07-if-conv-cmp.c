// Test: Check if conv_int inside if condition works
// This isolates the if(conv < conv) pattern
int main(void) {
  int a = -1;
  int b = 0;
  // Both converted to unsigned long: -1 -> ULONG_MAX, 0 -> 0
  // ULONG_MAX < 0 as unsigned = false = 0
  unsigned long ua = (unsigned long)a;
  unsigned long ub = (unsigned long)b;
  return ua < ub;
}

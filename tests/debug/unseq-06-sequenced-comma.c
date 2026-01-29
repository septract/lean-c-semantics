// Comma operator - should be sequenced, no race
// Should return 0 (no UB)
int x;

int main(void)
{
  (x = 1, x = 2);  // Comma sequences: x=1 then x=2
  return x - 2;    // x should be 2
}

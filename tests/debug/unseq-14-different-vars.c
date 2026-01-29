// Different variables - should NOT race
// EXPECTED: return 1 (no UB)
int x;
int y;

int main(void)
{
  // Write to different vars in unseq - no race
  (x = 1) + (y = 2);
  return x;
}

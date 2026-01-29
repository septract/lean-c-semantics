// Comma with read then write - sequenced, no race
// Should return 0 (no UB) - same as 0311
int x;

int main(void)
{
  (x, x = 0);  // Read x, then write x - sequenced by comma
}

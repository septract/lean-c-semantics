// CN test: Trusted function (no verification)
int trusted_read(int *p)
/*@ trusted; @*/
{
  return *p;
}

int main(void)
/*@ trusted; @*/
{
  int x = 42;
  return trusted_read(&x);
}

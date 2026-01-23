// CN test: Return literal (no memory or parameter access)
int fortytwo(void)
/*@ ensures return == 42; @*/
{
  return 42;
}

int main(void)
{
  return fortytwo();
}

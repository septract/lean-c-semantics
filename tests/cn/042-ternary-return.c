// CN test: Conditional return with ternary in spec
// From cn-tutorial: cond_1.c
// Tests: ternary conditional operator (? :) in CN spec expressions
// NEEDS: ternary conditional in spec parser, typed literals (0i32, 1i32)

int cond_return(int i)
/*@ ensures
      return == (i == 0i32 ? 0i32 : 1i32); @*/
{
  if (i == 0) {
    return 0;
  } else {
    return 1;
  }
}

int main(void)
{
  return cond_return(0);
}

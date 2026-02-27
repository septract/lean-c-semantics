// Test: cn_have ghost statement - assert a logical fact mid-function
// cn_have introduces a constraint that the type checker can use downstream

int add_bounded(int x, int y)
/*@ requires x >= 0i32; x <= 100i32;
             y >= 0i32; y <= 100i32;
    ensures return == x + y; @*/
{
    int sum = x + y;
    /*@ cn_have(sum == x + y); @*/
    return sum;
}

int main(void)
/*@ trusted; @*/
{
    return add_bounded(3, 4);
}

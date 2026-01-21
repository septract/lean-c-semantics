// Test: Multiple constraints in spec
// Tests handling of multiple requires/ensures clauses

int bounded_add(int x, int y)
/*@ requires 0 <= x;
             x < 1000;
             0 <= y;
             y < 1000;
    ensures return == x + y;
            0 <= return;
            return < 2000; @*/
{
    return x + y;
}

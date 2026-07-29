// Test: Separation failure - try to access a consumed resource
// The requires takes ownership of p but does not return it in ensures.
// This should fail because the resource is consumed (leaked).

void consume_resource(int *p)
/*@ requires take v = RW<int>(p); @*/
/*@ ensures true; @*/
{
    *p = 0;
}

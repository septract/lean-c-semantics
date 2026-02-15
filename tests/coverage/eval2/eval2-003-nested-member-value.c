// Test: nested struct value member access
// Exercises: PEmemberof — nested member extraction from struct rvalue
struct Inner { int a; int b; };
struct Outer { struct Inner in; int c; };
struct Outer make(void) { struct Outer o = {{1, 2}, 3}; return o; }
int main(void) { return make().in.a + make().in.b + make().c - 6; }

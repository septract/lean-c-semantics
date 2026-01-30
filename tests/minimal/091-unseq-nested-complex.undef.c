// Complex nested unsequenced expression - RACE (UB035)
// Read of x and write of x in unsequenced subexpressions
int x, y, z;

int main(void) {
    z = (x + (y = 0)) + (x = 0);  // UB: read of x unsequenced with write of x
}

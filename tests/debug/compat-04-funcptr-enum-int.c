// Test: function pointer cast between enum and int parameter types
// Calling through int(*)(int) that points to int(*)(enum color)
// Both Cerberus and our interpreter detect UB041 here - the function
// types are incompatible at the Function type level
enum color { RED, GREEN, BLUE };

int process_color(enum color c) {
    return (int)c + 10;
}

int main(void) {
    int (*fp)(int) = (int (*)(int))process_color;
    return fp(2);  // UB041: function_not_compatible
}

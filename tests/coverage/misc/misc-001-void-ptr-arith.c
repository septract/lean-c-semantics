// Test: void pointer arithmetic (GNU extension)
// Exercises: is_void branch in array_shift_ptrval (impl_mem.ml)
// Void* arithmetic treats void* like char* at byte granularity.
int main(void) {
    char data[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    void *vp = data;
    vp = vp + 3;  // GNU extension: void* arithmetic at byte granularity
    return *(char*)vp == 4 ? 0 : 1;
}

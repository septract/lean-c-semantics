// struct-003-struct-array-member.c
// Struct with an array member. Access array elements via struct.
// Exercises: PEstruct with array-typed member, PEmemberof + array subscript.

struct WithArray {
    int arr[5];
    int x;
};

int main(void) {
    struct WithArray s;
    s.arr[0] = 1;
    s.arr[1] = 2;
    s.arr[2] = 3;
    s.arr[3] = 4;
    s.arr[4] = 5;
    s.x = 100;

    int sum = s.arr[0] + s.arr[1] + s.arr[2] + s.arr[3] + s.arr[4] + s.x;
    // 1 + 2 + 3 + 4 + 5 + 100 = 115
    return sum;
}

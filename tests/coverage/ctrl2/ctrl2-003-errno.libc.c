// Test: errno access exercises process_impl_proc "errno" path
// Exercises: core_reduction.ml process_impl_proc errno case
#include <errno.h>
int main(void) {
    errno = 0;
    return errno == 0 ? 0 : 1;
}

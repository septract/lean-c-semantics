// misc-007-float-compare-branches.c
// Exercise float le_fval, ge_fval, gt_fval both-branch paths in core_eval.ml
// Need both true and false results for each float comparison
int main(void) {
    double a = 1.5;
    double b = 2.5;
    double c = 2.5;
    // <= true and false
    if (!(a <= b)) return 1;  // true
    if (b <= a)    return 2;  // false
    // >= true and false
    if (!(b >= a)) return 3;  // true
    if (a >= b)    return 4;  // false
    // > true and false
    if (!(b > a))  return 5;  // true
    if (a > b)     return 6;  // false
    // Equal
    if (!(b <= c)) return 7;  // le true (equal)
    if (!(b >= c)) return 8;  // ge true (equal)
    return 0;
}

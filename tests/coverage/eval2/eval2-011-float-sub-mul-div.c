// Test: float subtraction, multiplication, and division
// Exercises: float arithmetic (OpSub, OpMul, OpDiv) in evaluator
int main(void) {
  double a = 10.0;
  double b = 3.0;
  double sub = a - b;
  double mul = a * b;
  double div = a / b;
  return (int)sub == 7 && (int)mul == 30 && (int)div == 3 ? 0 : 1;
}

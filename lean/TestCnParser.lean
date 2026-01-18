/-
  Test the CN specification parser
-/
import CerbLean.CN.Parser

open CerbLean.CN.Parser

def testCases : List (String × String) := [
  -- Simple requires/ensures
  ("simple owned",
   " requires take v = Owned<int>(p);
     ensures take v2 = Owned<int>(p);
             v == v2;
             return == v; "),

  -- Just requires
  ("requires only",
   "requires take x = Owned<int>(ptr);"),

  -- Just ensures
  ("ensures only",
   "ensures take y = Owned<int>(q); y > 0;"),

  -- Constraint with binary ops
  ("binary ops",
   "requires x > 0; x < 100;"),

  -- Function call in expression
  ("function call",
   "ensures return == foo(x, y);"),

  -- Member access
  ("member access",
   "requires p->field == 42;"),

  -- Trusted function
  ("trusted",
   "trusted;"),

  -- Empty spec
  ("empty", "")
]

def main : IO UInt32 := do
  IO.println "=== CN Parser Tests ==="
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  for (name, input) in testCases do
    IO.print s!"Test '{name}': "
    match parseFunctionSpec input with
    | .ok spec =>
      IO.println "PASS"
      IO.println s!"  requires: {spec.requires.clauses.length} clauses"
      IO.println s!"  ensures: {spec.ensures.clauses.length} clauses"
      IO.println s!"  trusted: {spec.trusted}"
      passed := passed + 1
    | .error e =>
      IO.println s!"FAIL: {e}"
      failed := failed + 1
    IO.println ""

  IO.println "=== Summary ==="
  IO.println s!"Passed: {passed}"
  IO.println s!"Failed: {failed}"

  return if failed > 0 then 1 else 0

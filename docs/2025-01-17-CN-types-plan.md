User thoughts: 

We're going to plan a fun project - adding separation logic specifications to CerbLean. Here's a rough plan: 

- CN is an existing verification tool built on top of Cerberus https://github.com/rems-project/cn
- CN works by defining a refinement type system to Cerberus Core 
- We probably want to 
  1. research CN and figure out how it interacts with the Cerberus pipeline
  2. Work out how to run CN and export Core decorated with types
  3. Make sure those types are exported in our Cerberus JSON output 
  4. Define an AST for CN refinement types extending the current Lean Core AST 
  5. Parse CN annotations in JSON into types in the Core AST
  6. Make sure we can round-trip annotations - extend the pretty printer to show CN types 
  7. Define the CN typing rules in Lean - this requires at various points reasoning about judgements 
    - we can defer for now discharging those judgements, or do them with LeanSMT 
  8. Define a soundness theorem for CN - every CN type defines a refinement type over heap states
  9. (big task) prove the CN type system sound wrt the interpreter 


Things to find: 
* The CN formalization in Coq / Rocq 
* CN research papers
* The CN tutorial 

Claude's work below
~~~~~~~~~~~~~~~~~~~

## Key Resources Found

### Papers
- **POPL 2023**: "CN: Verifying Systems C Code with Separation-Logic Refinement Types"
  - https://www.cl.cam.ac.uk/~cp526/popl23.html
  - Foundational paper introducing CN
- **POPL 2025**: "Fulminate: Testing CN Separation-Logic Specifications in C"
  - https://dl.acm.org/doi/10.1145/3704879
  - Runtime testing of specifications

### Supplementary Materials
- Kernel type system definitions: https://www.cl.cam.ac.uk/~cp526/popl23_defns.pdf
- Soundness proof: https://www.cl.cam.ac.uk/~cp526/popl23_soundness.pdf

### Tutorial
- https://rems-project.github.io/cn-tutorial/

### Coq Formalization
The CN repo has a `coq/` directory with partial formalization:
- `coq/Cerberus/` (11 files): Core.v, Ctype.v, Memory.v, Undefined.v, etc.
- `coq/Cn/` (27 files): CNDefinition.v, BaseTypes.v, Resource.v, LogicalConstraints.v, etc.
- `coq/Reasoning/` (4 files): ProofAutomation.v, ResourceInference.v

**Note**: This is a formalization of the type system, NOT a foundational proof connecting to the implementation.

---

## CN Pipeline Architecture

```
C source code with CN annotations
    │
    ▼
[Preprocessing] → C with macro expansion
    │
    ▼
[C Parsing (CABS)] → C Abstract Syntax Tree
    │
    ▼
[Frontend elaboration] → AIL (Annotated Intermediate Language)
    │
    ▼
[Core Translation] → Core (Cerberus intermediate representation)
    │
    ▼
[Parse specifications] → Extract CN magic comments from source
    │
    ▼
[core_to_mucore] → muCore (CN-normalized Core with specifications attached)
    │
    ▼
[Type Checking] → Check specs, infer resources, generate constraints
    │
    ▼
[Verification / Fulminate / Coq Export]
```

---

## Key Finding: Core vs muCore

**Cerberus Core** does NOT carry CN specifications. The CN specs are:
1. Parsed into CABS as magic comments
2. Carried through AIL in the `sigma` record
3. **Lost** during AIL → Core translation

**CN's muCore** is a separate IR that:
1. Takes Cerberus Core as input
2. Parses magic comment annotations
3. Attaches specifications to functions
4. Adds type annotations to all expressions

This means we should export **muCore** from CN, not try to thread specs through Cerberus Core.

---

## muCore File Structure

```ocaml
type file = {
  main: Sym.t option;                    (* Main entry point *)
  tagDefs: tag_definitions;              (* Struct/union definitions *)
  globs: global_definitions;             (* Global variables *)
  funs: function_map;                    (* Functions WITH SPECS ATTACHED *)
  extern: extern_map;                    (* External symbols *)
  stdlib_syms: sym list;                 (* Library symbols *)
  resource_predicates: predicate list;   (* Ownership specs *)
  logical_predicates: function list;     (* Logical functions *)
  datatypes: datatype list;              (* User-defined datatypes *)
  lemmata: lemma list;                   (* Proof lemmas *)
  call_funinfo: funinfo_map;             (* Function signatures *)
}
```

---

## CN Specification Syntax (Examples)

### Simple Function Contract
```c
int division(int x, int y)
/*@ requires y != 0i32;
    ensures return == x/y; @*/
{
  return x / y;
}
```

### Datatype Definitions
```c
/*@ datatype seq {
      Seq_Nil {},
      Seq_Cons {i32 head, datatype seq tail}
    } @*/
```

### Recursive Predicates
```c
/*@ predicate [rec] (datatype seq) IntList(pointer p) @*/
```

### Resource Ownership (Iterated Separating Conjunction)
```c
void swap_pair(int *pair)
/*@ requires take pairStart = each (i32 j; 0i32 <= j && j < 2i32)
                               {RW(array_shift(pair, j))};
    ensures  take pairEnd = each (i32 j; 0i32 <= j && j < 2i32)
                               {RW(array_shift(pair, j))};
             pairEnd[0i32] == pairStart[1i32];
             pairEnd[1i32] == pairStart[0i32]; @*/
```

### Trusted Functions
```c
int main() /*@ trusted; @*/
{
  ...
}
```

---

## CN Type System

### Base Types (`BaseTypes.t`)
| Type | Description |
|------|-------------|
| `Unit` | void/no value |
| `Bool` | boolean |
| `Integer` | unbounded integers |
| `Bits(sign, width)` | fixed-width (i32, u64, etc.) |
| `Real` | floating-point |
| `Loc` | pointers/locations |
| `Alloc_id` | allocation identifiers |
| `Struct(sym)` | named struct |
| `Record(fields)` | anonymous struct |
| `Datatype(sym)` | user-defined ADT |
| `Map(k, v)` | finite maps |
| `List(t)` | lists |
| `Tuple(ts)` | tuples |
| `Set(t)` | sets |

### Function Specifications (`ArgumentTypes.t`)
```ocaml
type 'i t =
  | Computational of (Sym.t * BT.t) * info * 'i t  (* Regular param *)
  | Ghost of (Sym.t * BT.t) * info * 'i t          (* Spec-only param *)
  | L of 'i LAT.t                                   (* Return type *)
```

### Return Types (`LogicalReturnTypes.t`)
```ocaml
type t =
  | Define of (Sym.t * IT.t) * info * t      (* Bind result *)
  | Resource of (Sym.t * (RT.t * BT.t)) * info * t  (* Ownership *)
  | Constraint of LC.t * info * t            (* Assertion *)
  | I                                        (* Done *)
```

### Logical Constraints (`LogicalConstraints.t`)
```ocaml
type t =
  | T of IT.t                              (* Simple constraint *)
  | Forall of (Sym.t * BT.t) * IT.t        (* Universal quantification *)
```

---

## Index Terms (IT) - The Heart of CN Specifications

Index terms are symbolic values used in specifications. They are the "language" of CN assertions.

```ocaml
type 'bt term =
  (* Basic *)
  | Const of const                              (* Literal constants *)
  | Sym of Sym.t                                (* Variables *)

  (* Arithmetic/Logic *)
  | Unop of unop * 'bt annot                    (* Negation, complement *)
  | Binop of binop * 'bt annot * 'bt annot      (* +, -, *, /, <, ==, && *)
  | ITE of 'bt annot * 'bt annot * 'bt annot    (* if-then-else *)

  (* Quantification *)
  | EachI of (int * (Sym.t * BaseTypes.t) * int) * 'bt annot

  (* Tuples *)
  | Tuple of 'bt annot list
  | NthTuple of int * 'bt annot

  (* Structs *)
  | Struct of Sym.t * (Id.t * 'bt annot) list
  | StructMember of 'bt annot * Id.t
  | StructUpdate of ('bt annot * Id.t) * 'bt annot

  (* Records (anonymous structs) *)
  | Record of (Id.t * 'bt annot) list
  | RecordMember of 'bt annot * Id.t
  | RecordUpdate of ('bt annot * Id.t) * 'bt annot

  (* Datatypes *)
  | Constructor of Sym.t * (Id.t * 'bt annot) list

  (* Pointers *)
  | MemberShift of 'bt annot * Sym.t * Id.t     (* &p->field *)
  | ArrayShift of { base; ct; index }            (* p + i *)
  | CopyAllocId of { addr; loc }                 (* Copy alloc ID *)
  | HasAllocId of 'bt annot

  (* Sizes *)
  | SizeOf of Sctypes.t
  | OffsetOf of Sym.t * Id.t

  (* Lists *)
  | Nil of BaseTypes.t
  | Cons of 'bt annot * 'bt annot
  | Head of 'bt annot
  | Tail of 'bt annot

  (* Type predicates *)
  | Representable of Sctypes.t * 'bt annot      (* Value fits in type *)
  | Good of Sctypes.t * 'bt annot               (* No trap representations *)
  | Aligned of { t; align }                      (* Alignment check *)
  | WrapI of IntegerTypes.t * 'bt annot         (* Wrap to width *)

  (* Maps (for arrays) *)
  | MapConst of BaseTypes.t * 'bt annot         (* Constant map *)
  | MapSet of 'bt annot * 'bt annot * 'bt annot (* Update *)
  | MapGet of 'bt annot * 'bt annot             (* Lookup *)
  | MapDef of (Sym.t * BaseTypes.t) * 'bt annot (* Comprehension *)

  (* Function application *)
  | Apply of Sym.t * 'bt annot list

  (* Binding *)
  | Let of (Sym.t * 'bt annot) * 'bt annot
  | Match of 'bt annot * ('bt pattern * 'bt annot) list
  | Cast of BaseTypes.t * 'bt annot
```

---

## Resource Requests

### Simple Predicates (`Predicate.t`)
```ocaml
type t = {
  name: name;           (* Owned(ct, init) | PName sym *)
  pointer: IT.t;        (* Memory location *)
  iargs: IT.t list;     (* Index arguments *)
}
```

### Quantified Predicates (`QPredicate.t`) - for arrays
```ocaml
type t = {
  name: name;
  pointer: IT.t;
  q: Sym.t * BT.t;      (* Quantified variable *)
  step: Sctypes.t;      (* Element stride *)
  permission: IT.t;     (* Guard: which indices are valid *)
  iargs: IT.t list;
}
```

### Ownership Names
- `Owned(ct, Init)` → read-write permission ("RW")
- `Owned(ct, Uninit)` → write-only permission ("W")
- `PName(sym)` → named user-defined predicate

---

## Key CN Source Files

| File | Purpose |
|------|---------|
| `lib/mucore.ml` | muCore AST definition |
| `lib/core_to_mucore.ml` | Core → muCore transformation |
| `lib/argumentTypes.ml` | Function spec structure |
| `lib/logicalReturnTypes.ml` | Postcondition structure |
| `lib/logicalConstraints.ml` | Constraint representation |
| `lib/resource.ml` | Ownership predicates |
| `lib/request.ml` | Resource requests |
| `lib/baseTypes.ml` | CN base types |
| `lib/terms.ml` | Index term representation |
| `lib/indexTerms.ml` | Annotated index terms |
| `lib/typing.ml` | Type checking |
| `lib/check.ml` | Verification |
| `lib/compile.ml` | CN expr → index terms |
| `lib/parse.ml` | Specification parsing |
| `bin/verify.ml` | Main verification entry |

---

## Existing JSON Support in CN

**Good news**: CN uses Yojson as a dependency.

**Bad news**: The core types (muCore, terms, resources) do NOT have `[@@deriving yojson]` annotations.

We would need to add JSON derivations to:
- `BaseTypes.t`
- `terms.ml` term type
- `IndexTerms.t`
- `LogicalConstraints.t`
- `Request.t` / `Resource.t`
- `ArgumentTypes.t` / `ReturnTypes.t`
- `Mucore.file` and related types

---

## Design Decision: Export Core + Raw CN Annotations

CN annotations survive into Core as `cerb::magic` attributes. The raw annotation strings are stored in `Aattrs` annotations on Core expressions.

**Key finding**: CN itself reads these via `A.get_cerb_magic_attr` during `core_to_mucore`. We can do the same.

**Chosen approach:**
```
C + CN specs → Cerberus → Core JSON (with magic strings) → Lean Parser → Core + raw strings → CN Parser (Lean) → Core + structured specs
```

**Implementation steps:**
1. Modify `json_core.ml` to export `cerb::magic` attribute strings
2. Extend Lean Core parser to capture raw annotation strings
3. Write CN annotation parser in Lean
4. Define Lean types for CN specs (requires, ensures, predicates, etc.)

**Advantages over exporting muCore:**
- Keep existing Core parser mostly unchanged
- Incremental: CN parsing is a separate layer
- CN annotation grammar is simpler than full muCore AST
- We control parsing entirely in Lean
- No need to modify CN codebase

---

## Minimal CN Subset (v0.1)

Start with a tiny subset to prove the pipeline works, then expand.

### Grammar

```
spec ::= "requires" clause* "ensures" clause*

clause ::= "take" id "=" resource ";"
         | expr ";"

resource ::= "Owned" "<" ctype ">" "(" expr ")"

expr ::= id                      -- variable
       | integer                 -- literal
       | expr binop expr         -- arithmetic/comparison
       | "return"                -- return value (in ensures)

binop ::= "==" | "!=" | "+" | "-" | "*" | "<" | "<=" | ">" | ">="
```

### Examples

```c
void inc(int *p)
/*@ requires take v = Owned<int>(p);
    ensures take v2 = Owned<int>(p);
            v2 == v + 1; @*/
{
  *p = *p + 1;
}

int read(int *p)
/*@ requires take v = Owned<int>(p);
    ensures take v2 = Owned<int>(p);
            v == v2;
            return == v; @*/
{
  return *p;
}

void swap(int *a, int *b)
/*@ requires take va = Owned<int>(a);
             take vb = Owned<int>(b);
    ensures take va2 = Owned<int>(a);
            take vb2 = Owned<int>(b);
            va2 == vb;
            vb2 == va; @*/
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
```

### Semantics (informal)

- `take x = Owned<T>(p)` means: "the heap contains a cell at pointer `p` of type `T`, bind its value to `x`, and transfer ownership"
- In `requires`: consume ownership from caller's heap
- In `ensures`: produce ownership back to caller
- Expressions in clauses are pure assertions over bound values

### What This Tests

1. **JSON export**: Magic annotation strings in Core JSON
2. **Lean parsing**: Parse `requires`/`ensures`/`take`/`Owned`
3. **AST representation**: Define `CNSpec`, `CNClause`, `CNResource` types
4. **Pretty-printing**: Round-trip the specs
5. **Semantic interpretation**: `Owned<T>(p)` = memory model has allocation at `p`
6. **Soundness sketch**: Precondition on input heap → postcondition on output heap

### Deferred Features

- Quantified resources (`each`)
- User-defined predicates
- Ghost arguments
- Datatypes and lists
- Logical functions
- Loop invariants

---

## Implementation Plan

### Phase 1: JSON Export (Cerberus)
- [ ] Modify `json_core.ml` to export `cerb::magic` attributes
- [ ] Test with simple CN-annotated C file

### Phase 2: Lean Parser
- [ ] Define `CNSpec` types in Lean
- [ ] Extend Core parser to capture raw annotation strings
- [ ] Write CN annotation parser (for minimal subset)
- [ ] Unit tests for parser

### Phase 3: Pretty-Printer
- [ ] Extend pretty-printer to show CN specs
- [ ] Verify round-trip: parse → print → parse

### Phase 4: Semantic Model
- [ ] Define what `Owned<T>(p)` means in terms of memory model
- [ ] Define spec satisfaction: when does a heap satisfy a spec?

### Phase 5: Type Checking
- [ ] Implement CN type checking for minimal subset
- [ ] Check that requires/ensures are well-formed
- [ ] Generate verification conditions

### Phase 6: Soundness
- [ ] State soundness theorem
- [ ] Prove for simple cases

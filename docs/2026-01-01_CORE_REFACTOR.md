# Core Types Audit Plan

This document tracks the audit of `lean/CToLean/Core/*.lean` against Cerberus source files to ensure exact correspondence.

## Audit Comment Format

Every type and function should have an audit comment:

```lean
/-- Corresponds to: cerberus/frontend/[file] lines X-Y
    Type/Function: [name in Cerberus]
    Audited: 2025-12-31
    Deviations: None (or list any with justification)
-/
```

## Summary of Findings

| File | Status | Issues Found |
|------|--------|--------------|
| `Sym.lean` | Missing audit comments | Structure simplified vs Cerberus |
| `Annot.lean` | Missing audit comments | Missing fields |
| `Ctype.lean` | Missing audit comments | FloatingType mismatch, Function params missing is_register |
| `Undefined.lean` | Missing audit comments | Only ~15 variants vs Cerberus's ~200+ |
| `Types.lean` | Has audit comments | Needs verification |
| `Value.lean` | Has audit comments | Needs verification |
| `Expr.lean` | Has audit comments | Linux actions intentionally excluded |
| `File.lean` | Partial audit comments | Missing loop_attributes, calling_convention |

---

## Phase 1: Ctype.lean (MAJOR)

**Cerberus Reference**:
- `cerberus/frontend/model/integerType.lem` lines 10-35
- `cerberus/frontend/model/ctype.lem` lines 11-63

### Issue 1: FloatingType (ctype.lem:11-18)

**Cerberus**:
```lem
type realFloatingType = Float | Double | LongDouble
type floatingType = RealFloating of realFloatingType
```

**Current Lean**: Missing `RealFloating` wrapper

### Issue 2: Function Parameters (ctype.lem:47-49)

**Cerberus**:
```lem
| Function of (qualifiers * ctype) * list (qualifiers * ctype * bool) * bool
```

**Current Lean**: Missing `is_register` bool in parameter tuples

### Issue 3: Ctype wrapper (ctype.lem:62-63)

**Cerberus**:
```lem
and ctype = Ctype of list Annot.annot * ctype_
```

**Current Lean**: Missing annotation list wrapper

### Actions
1. Rename current `Ctype` to `Ctype_` (inner type)
2. Create new `Ctype` structure with `annots : Annots` and `ty : Ctype_`
3. Add `RealFloatingType` and make `FloatingType` match Cerberus structure
4. Add `is_register` bool to function parameters
5. Update Parser.lean and PrettyPrint.lean
6. Update all Ctype usages throughout codebase

---

## Phase 2: Sym.lean

**Cerberus Reference**: `cerberus/frontend/model/symbol.lem` lines 126-128

### Current Lean
```lean
structure Sym where
  id : Nat
  name : Option String := none
```

### Cerberus
```lem
type sym = Symbol of digest * nat * symbol_description
```

### Discrepancies
- **Missing**: `digest` field (translation unit identifier)
- **Missing**: `symbol_description` type (lines 77-88)
- **Identifier**: Missing `Loc` field

### Actions
1. Add `digest` field (as `String`)
2. Add `symbol_description` enum
3. Fix `Identifier` to include `Loc`

---

## Phase 3: Undefined.lean

**Cerberus Reference**: `cerberus/frontend/model/undefined.lem` lines 21-733

### Decision
Use ~50 key variants + `other(name: String)` catch-all (not full 200+).

### Key Variants to Include
- Memory UBs: UB009, UB010, UB043
- Integer UBs: UB045a/b/c, UB051a/b, UB052a/b
- Pointer UBs: UB046, UB048, UB053
- Function UBs: UB038, UB041, UB088
- CERB extensions: UB_CERB001-005

---

## Phase 4: File.lean

**Cerberus Reference**: `cerberus/frontend/ott/core-ott/core.ott` lines 552-563

### Missing Fields
- `loop_attributes` (core.ott:561)
- `calling_convention` (core.lem:406-408)
- `marker_env` in FunDecl.proc (core.ott:496)

---

## Phase 5-8: Verification

Files with existing audit comments need verification:
- **Types.lean**: Verify line numbers, add Iop/MemoryOrder sources
- **Value.lean**: Add memory type source references
- **Expr.lean**: Verify all Pexpr/Expr variants present
- **Annot.lean**: Verify completeness

---

## Execution Order

### Priority 1: Major Structural Changes
1. **Ctype.lean**: Annotation wrapper + fixes (cascades to many files)
2. **Sym.lean**: Add symbol_description, fix Identifier
3. **Undefined.lean**: Add key UB variants

### Priority 2: Missing Fields
4. **File.lean**: Add missing fields
5. **Annot.lean**: Verify completeness

### Priority 3: Verification
6. **Types.lean**: Verify audit comments
7. **Value.lean**: Add source references
8. **Expr.lean**: Verify variants

### Priority 4: Dependent Files
9. **Parser.lean**: Update for type changes
10. **PrettyPrint.lean**: Update for type changes

---

## Files to Modify

| File | Changes |
|------|---------|
| `Core/Ctype.lean` | **Major**: Add annotation wrapper, fix FloatingType, add is_register |
| `Core/Sym.lean` | Add digest, symbol_description; fix Identifier |
| `Core/Undefined.lean` | Add ~50 key UB variants + catch-all |
| `Core/File.lean` | Add missing fields |
| `Core/Annot.lean` | Add audit comments, verify completeness |
| `Core/Types.lean` | Verify audit comments |
| `Core/Value.lean` | Add memory type source references |
| `Core/Expr.lean` | Verify all variants |
| `Parser.lean` | Update for type changes |
| `PrettyPrint.lean` | Update for type changes |

---

## Validation

After each phase:
```bash
make lean                          # Ensure compilation
make test-unit                     # Parser smoke tests
./scripts/test_pp.sh --max 100     # Pretty-printer tests
./scripts/test_parser.sh --max 100 # Parser tests
```

Final validation:
```bash
make test  # Full test suite
```

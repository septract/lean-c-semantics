# Audit of @lean/CToLean/Parser.lean

**Date:** 2025-12-26
**Auditor:** Gemini

## Overview
This audit reviews the correctness, robustness, and completeness of the Lean 4 parser for Cerberus Core JSON output. The parser is critical for the C-to-Lean translation pipeline.

## Critical Issues

### 1. Incorrect Parsing of `PtrMemberShift` Memop
The parser incorrectly maps the `PtrMemberShift` memory operation to `ptrArrayShift`, discarding the structure tag and member identifier.
**Location:** `parseMemop`
**Current Code:**
```lean
  if s.startsWith "PtrArrayShift[" then
    -- This is actually PtrMemberShift with [tag, member] info
    -- For now, just treat as ptrArrayShift since parsing brackets is complex
    .ok .ptrArrayShift
```
**Impact:** Logic involving structure member access via pointers will be incorrect or ambiguous in the Lean AST.
**Recommendation:** Implement proper parsing of the string to extract the tag and member. Note that `Sym` reconstruction from a string name alone (if the ID is missing) might be impossible without a symbol table or if the string format doesn't include the ID. If the string format is `PtrArrayShift[tag_name, member_name]`, we may only be able to create a partial `Sym` or need to look up the tag.

### 2. Data Loss in Struct and Union Values
The values of struct members and union members are explicitly ignored and set to `unspecified`.
**Location:** `parseObjectValue` (cases `OVstruct`, `OVunion`)
**Current Code:**
```lean
        -- Value is a string representation of mem_value - store as unspecified for now
        pure { name := name, ty := ctype, value := .unspecified ctype : StructMember }
```
**Impact:** Constant structs and unions in the source C code will lose their initialization values in Lean.
**Recommendation:** Implement a `parseMemValueString` function to parse the pretty-printed `mem_value` string provided in the JSON, or modify Cerberus to export structured JSON for these values.

### 3. Missing `File` Fields
The `parseFile` function does not populate the `stdlib`, `impl`, and `extern` fields of the `File` structure.
**Location:** `parseFile`
**Impact:** Standard library functions, implementation-defined constants, and external symbols are not available in the parsed `File` object.
**Recommendation:** Add parsing logic for these fields. For `stdlib`, it likely follows the `FunMap` structure. For `impl` and `extern`, correct parsers for `ImplDefs` and external mappings are needed.

## Major Issues

### 4. Brittle `OVpointer` Parsing & Missing Provenance
Pointer values are parsed from strings like `NULL(void*)` or hex addresses, which is brittle. Crucially, provenance information is completely ignored (`prov := .none`).
**Location:** `parseObjectValue` (case `OVpointer`)
**Current Code:**
```lean
        .ok (.pointer { prov := .none, base := .concrete none addr })
```
**Impact:** Pointer provenance is lost, which is critical for accurate memory model semantics (PNVI).
**Recommendation:** If the JSON string contains provenance (e.g. `(prov_id, 0xaddr)`), it must be parsed. Requires reverse-engineering the string format used by Cerberus JSON export for pointers.

### 5. Brittle `parseCtypeStr`
The `parseCtypeStr` function manually parses C type strings. This is fragile and likely incomplete (e.g., complex function pointers, arrays in partial syntax).
**Location:** `parseCtypeStr`
**Impact:** `OVpointer` values containing type information (like NULL pointers) may be parsed incorrectly or default to `void`.
**Recommendation:** Use the structured `ctype` field if available in the JSON for these values, or improve the string parser to cover more cases (or use a parser combinator library).

### 6. Simplified Annotation Parsing
Only `loc` annotations are parsed. Other annotations (UIDs, etc.) are ignored.
**Location:** `parseAnnots`
**Impact:** Debugging information or other metadata attached to expressions is lost.
**Recommendation:** Iterate over all fields or a specific `annots` list in the JSON to capture all annotation types.

## Minor Issues

### 7. Missing `parseImplDecl`
There is no function to parse implementation definitions, which contributes to the missing `impl` field in `File`.

### 8. `parseMemop` String Matching
Relying on string matching for `Memop` (e.g., "PtrEq") is prone to case-sensitivity mismatches if Cerberus output changes slightly.

## Recommendations for Immediate Fixes

### Fix 1: Add `stdlib` and `extern` parsing to `parseFile`
Assuming `stdlib` has the same structure as `funs` (FunMap) and `extern` has a predictable structure.

```lean
-- In parseFile
  let stdlibJ ← getArr j "stdlib" -- Verify field name in JSON
  let stdlib ← stdlibJ.toList.mapM parseFunDecl

  -- ... (parse externs if structure is known)

  .ok {
    -- ...
    stdlib := stdlib
    -- ...
  }
```

### Fix 2: Improve `PtrMemberShift` parsing
If the format is `PtrArrayShift[tag,member]`, try to parse it.

```lean
-- Inside parseMemop
  else if s.startsWith "PtrArrayShift[" && s.endsWith "]" then
    let content := (s.drop 14).dropRight 1
    match content.splitOn "," with
    | [tagStr, memberStr] =>
       -- NOTE: We only have the tag name, not the ID. 
       -- Creating a Sym with ID 0 might be dangerous if IDs matter for uniqueness.
       let tag := { id := 0, name := some tagStr.trim : Sym } 
       let member := { name := memberStr.trim : Identifier }
       .ok (.ptrMemberShift tag member)
    | _ => .error s!"invalid PtrArrayShift format: {content}"
```

### Fix 3: Robust `OVpointer` parsing
Expand `parseObjectValue` to handle provenance if present in the string.

```lean
-- Conceptual fix
      else if valStr.startsWith "(" && valStr.contains "," then
         -- Handle (prov, addr) format
         -- ... parsing logic ...
         .ok (.pointer { prov := parsedProv, base := .concrete none parsedAddr })
```

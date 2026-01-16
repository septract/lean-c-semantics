# JSON Pointer Value Serialization Fix

## Problem

Currently, Cerberus exports pointer values as pretty-printed strings in JSON:

```json
{
  "tag": "OVpointer",
  "value": "Cfunction(add)"
}
```

This loses critical information:
- **Symbol IDs**: The numeric ID that uniquely identifies symbols is lost
- **Provenance**: Allocation IDs for concrete pointers are embedded in strings
- **Addresses**: Hex addresses require string parsing

The Lean parser must create symbols with `id := 0` because the ID isn't available, which breaks function pointer round-tripping through memory (address 0 = NULL).

## Root Cause

In `cerberus/ocaml_frontend/pprinters/json_core.ml` line 310:

```ocaml
| OVpointer pval ->
    obj "OVpointer" [("value", `String (pp_to_string (Impl_mem.pp_pointer_value pval)))]
```

The code calls `Impl_mem.pp_pointer_value` which converts the entire pointer to a string, discarding structured data.

## Solution: Use `case_ptrval` Interface

The `Memory` module type (in `memory_model.ml:75-78`) provides a **modular** way to decompose pointer values:

```ocaml
val case_ptrval: pointer_value ->
 (* null pointer *) (Ctype.ctype -> 'a) ->
 (* function pointer *) (Symbol.sym option -> 'a) ->
 (* concrete pointer *) (Nat_big_num.num option -> Nat_big_num.num -> 'a) -> 'a
```

This allows structured JSON serialization without depending on the concrete memory model's internal types.

## Implementation Plan

### Step 1: Add `json_pointer_value` function in `json_core.ml`

```ocaml
let json_pointer_value (pval : Impl_mem.pointer_value) : Yojson.Safe.t =
  Impl_mem.case_ptrval pval
    (* null pointer *)
    (fun cty -> `Assoc [
      ("tag", `String "PVnull");
      ("ctype", json_ctype cty)
    ])
    (* function pointer *)
    (fun sym_opt -> `Assoc [
      ("tag", `String "PVfunction");
      ("sym", match sym_opt with
        | Some sym -> json_sym sym
        | None -> `Null)
    ])
    (* concrete pointer *)
    (fun alloc_id_opt addr -> `Assoc [
      ("tag", `String "PVconcrete");
      ("alloc_id", match alloc_id_opt with
        | Some id -> `String (Nat_big_num.to_string id)
        | None -> `Null);
      ("addr", `String (Nat_big_num.to_string addr))
    ])
```

### Step 2: Update `OVpointer` serialization

Change line 310 from:
```ocaml
| OVpointer pval ->
    obj "OVpointer" [("value", `String (pp_to_string (Impl_mem.pp_pointer_value pval)))]
```

To:
```ocaml
| OVpointer pval ->
    obj "OVpointer" [("value", json_pointer_value pval)]
```

### Step 3: Update Lean parser (`Parser.lean`)

Update the `OVpointer` parsing (around line 670) to handle structured JSON:

```lean
| "OVpointer" =>
  let valJson ← getObj j "value"
  let tag ← getStr valJson "tag"
  match tag with
  | "PVnull" =>
    let cty ← parseCtype valJson "ctype"
    .ok (.pointer { prov := .none, base := .null cty })
  | "PVfunction" =>
    let symJson ← getObj valJson "sym"
    let sym ← parseSym symJson  -- gets id and name
    .ok (.pointer { prov := .none, base := .function sym })
  | "PVconcrete" =>
    let allocId ← getOptNat valJson "alloc_id"
    let addr ← getNat valJson "addr"
    let prov := match allocId with
      | some id => .some id
      | none => .none
    .ok (.pointer { prov := prov, base := .concrete none addr })
  | _ => .error s!"unknown pointer tag: {tag}"
```

## Output Format

The new JSON format will be:

**Function pointer:**
```json
{
  "tag": "OVpointer",
  "value": {
    "tag": "PVfunction",
    "sym": { "id": 530, "name": "add" }
  }
}
```

**Null pointer:**
```json
{
  "tag": "OVpointer",
  "value": {
    "tag": "PVnull",
    "ctype": { ... }
  }
}
```

**Concrete pointer:**
```json
{
  "tag": "OVpointer",
  "value": {
    "tag": "PVconcrete",
    "alloc_id": "5",
    "addr": "4096"
  }
}
```

## Modularity Analysis

**Good news**: This approach is modular!

- Uses `case_ptrval` from the `Memory` module interface (not concrete types)
- Works with any memory model that implements the interface
- No dependency on `impl_mem.ml` internal types like `PVfunction`, `PVconcrete`

**Limitation**: The `case_ptrval` interface doesn't expose:
- `Prov_symbolic` (PNVI-ae-udi) - returns `None` for alloc_id
- `Prov_device` - also returns `None`
- Union member info in `PVconcrete` - the `identifier option` is not exposed

For now, this is acceptable since we're targeting the concrete memory model for differential testing.

## Files to Modify

1. **`cerberus/ocaml_frontend/pprinters/json_core.ml`**
   - Add `json_pointer_value` function
   - Update `OVpointer` case in `json_object_value`

2. **`lean/CToLean/Parser.lean`**
   - Update `OVpointer` parsing to handle structured JSON
   - Ensure `parseSym` extracts both `id` and `name`

## Testing

After implementation:
1. Regenerate JSON for test files: `cerberus --json_core_out=test.json tests/minimal/056-func-ptr.c`
2. Verify JSON contains structured pointer data
3. Run interpreter tests: `./scripts/test_interp.sh tests/minimal`
4. Function pointer test (056-func-ptr) should now pass

## Future Considerations

1. **Integer values**: Similarly affected (`OVinteger` uses `pp_integer_value_for_core`)
2. **Memory values**: `OVstruct`/`OVunion` member values use `pp_mem_value`
3. Consider adding `json_integer_value` and `json_mem_value` for full structured export

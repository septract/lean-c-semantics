# JSON Export Remaining Fixes

**Date:** 2026-01-02
**Status:** COMPLETED

## Completion Summary

All structured JSON export issues have been fixed:

- ✅ **Issue 1: Memop serialization** - Pattern matching on memop constructors, PtrMemberShift exports struct_tag and member
- ✅ **Issue 2: Pure memop serialization** - Included in memop fix
- ✅ **Issue 3: mem_value serialization** - Uses `case_mem_value` for recursive structured export
- ✅ **Issue 4: impl field** - Now exported with constant name and declaration
- ✅ **Issue 5: extern field** - Now exported with identifier, symbols, and linking_kind

Test results: 100% parser success rate, 100% pretty-printer match rate.

---

## Original Plan (for reference)

## Overview

The Cerberus JSON export currently uses string representations for several data types that should be structured JSON. This document describes the remaining issues and the changes needed to fix them.

All changes are in the Cerberus submodule, primarily in:
- `cerberus/ocaml_frontend/pprinters/json_core.ml` - JSON serialization
- `cerberus/ocaml_frontend/memory_model.ml` - Memory model interface (if needed)

## Issues to Fix

### 1. Memop Serialization (PtrMemberShift)

**Current State:** All memops are serialized as pretty-printed strings.

**Location:** `json_core.ml:640-641`
```ocaml
let json_memop (op : 'sym Mem_common.generic_memop) : Yojson.Safe.t =
  `String (pp_to_string (Pp_mem.pp_memop op))
```

**Problem:** `PtrMemberShift` has associated data (struct tag symbol and member identifier) that is embedded in the string as `"PtrArrayShift[tag, member]"`. This data is lost/hard to parse.

**Note:** There's also a bug in `pp_mem.ml:70-71` where `PtrMemberShift` is printed as `"PtrArrayShift"` instead of `"PtrMemberShift"`.

**Type Definition:** From `mem_common.lem:371-404`
```ocaml
type generic_memop 'sym =
  | PtrEq | PtrNe | PtrLt | PtrGt | PtrLe | PtrGe
  | Ptrdiff | IntFromPtr | PtrFromInt | PtrValidForDeref | PtrWellAligned
  | PtrArrayShift
  | PtrMemberShift of 'sym * Symbol.identifier  (* HAS DATA *)
  | Memcpy | Memcmp | Realloc
  | Va_start | Va_copy | Va_arg | Va_end
  | Copy_alloc_id
  | CHERI_intrinsic of string * (Ctype.ctype * list Ctype.ctype)  (* HAS DATA *)
```

**Solution:** Replace string serialization with structured JSON:
```ocaml
let json_memop (op : Symbol.sym Mem_common.generic_memop) : Yojson.Safe.t =
  match op with
  | PtrEq -> `Assoc [("tag", `String "PtrEq")]
  | PtrNe -> `Assoc [("tag", `String "PtrNe")]
  | PtrLt -> `Assoc [("tag", `String "PtrLt")]
  | PtrGt -> `Assoc [("tag", `String "PtrGt")]
  | PtrLe -> `Assoc [("tag", `String "PtrLe")]
  | PtrGe -> `Assoc [("tag", `String "PtrGe")]
  | Ptrdiff -> `Assoc [("tag", `String "Ptrdiff")]
  | IntFromPtr -> `Assoc [("tag", `String "IntFromPtr")]
  | PtrFromInt -> `Assoc [("tag", `String "PtrFromInt")]
  | PtrValidForDeref -> `Assoc [("tag", `String "PtrValidForDeref")]
  | PtrWellAligned -> `Assoc [("tag", `String "PtrWellAligned")]
  | PtrArrayShift -> `Assoc [("tag", `String "PtrArrayShift")]
  | PtrMemberShift (tag_sym, member_id) ->
      `Assoc [
        ("tag", `String "PtrMemberShift");
        ("struct_tag", json_sym tag_sym);
        ("member", json_identifier member_id)
      ]
  | Memcpy -> `Assoc [("tag", `String "Memcpy")]
  | Memcmp -> `Assoc [("tag", `String "Memcmp")]
  | Realloc -> `Assoc [("tag", `String "Realloc")]
  | Va_start -> `Assoc [("tag", `String "Va_start")]
  | Va_copy -> `Assoc [("tag", `String "Va_copy")]
  | Va_arg -> `Assoc [("tag", `String "Va_arg")]
  | Va_end -> `Assoc [("tag", `String "Va_end")]
  | Copy_alloc_id -> `Assoc [("tag", `String "Copy_alloc_id")]
  | CHERI_intrinsic (name, (ret_ty, arg_tys)) ->
      `Assoc [
        ("tag", `String "CHERI_intrinsic");
        ("name", `String name);
        ("return_type", json_ctype ret_ty);
        ("arg_types", `List (List.map json_ctype arg_tys))
      ]
```

**Lean Parser Update:** Update `parseMemop` to handle structured JSON instead of strings.

---

### 2. Pure Memop Serialization

**Current State:** Pure memops are serialized as strings.

**Location:** `json_core.ml:394-395`
```ocaml
let json_pure_memop (op : Mem_common.pure_memop) : Yojson.Safe.t =
  `String (pp_to_string (Pp_mem.pp_pure_memop op))
```

**Type Definition:** From `mem_common.lem:360-369`
```ocaml
type pure_memop =
  | DeriveCap of derivecap_op * bool  (* HAS DATA *)
  | CapAssignValue
  | Ptr_tIntValue
  | ByteFromInt
  | IntFromByte
```

**Solution:** Same pattern as memop - structured JSON with tags:
```ocaml
let json_pure_memop (op : Mem_common.pure_memop) : Yojson.Safe.t =
  match op with
  | DeriveCap (derive_op, is_signed) ->
      `Assoc [
        ("tag", `String "DeriveCap");
        ("op", json_derivecap_op derive_op);
        ("is_signed", `Bool is_signed)
      ]
  | CapAssignValue -> `Assoc [("tag", `String "CapAssignValue")]
  | Ptr_tIntValue -> `Assoc [("tag", `String "Ptr_tIntValue")]
  | ByteFromInt -> `Assoc [("tag", `String "ByteFromInt")]
  | IntFromByte -> `Assoc [("tag", `String "IntFromByte")]
```

---

### 3. Struct/Union Member Values (mem_value)

**Current State:** Member values are serialized as pretty-printed strings.

**Location:** `json_core.ml:337-352`
```ocaml
| OVstruct (tag, members) ->
    obj "OVstruct" [
      ("struct_tag", json_sym tag);
      ("members", `List (List.map (fun (id, cty, mval) ->
        `Assoc [
          ("name", json_identifier id);
          ("ctype", json_ctype cty);
          ("value", `String (pp_to_string (Impl_mem.pp_mem_value mval)))  (* STRING! *)
        ]) members))
    ]
| OVunion (tag, id, mval) ->
    obj "OVunion" [
      ("union_tag", json_sym tag);
      ("member", json_identifier id);
      ("value", `String (pp_to_string (Impl_mem.pp_mem_value mval)))  (* STRING! *)
    ]
```

**Problem:** `mem_value` is an abstract type in the memory model interface. The JSON serializer can't pattern-match on its constructors directly.

**Type Definition:** From `memory/concrete/impl_mem.ml:310-317`
```ocaml
type mem_value =
  | MVunspecified of ctype
  | MVinteger of integerType * integer_value
  | MVfloating of floatingType * floating_value
  | MVpointer of ctype * pointer_value
  | MVarray of mem_value list
  | MVstruct of Symbol.sym * (Symbol.identifier * ctype * mem_value) list
  | MVunion of Symbol.sym * Symbol.identifier * mem_value
```

**Interface:** The `memory_model.ml` interface exposes `case_mem_value` for pattern matching:
```ocaml
val case_mem_value:
  mem_value ->
  (Ctype.ctype -> 'a) ->                                    (* unspecified *)
  (unit -> 'a) ->                                           (* concurrent read *)
  (Ctype.integerType -> integer_value -> 'a) ->             (* integer *)
  (Ctype.floatingType -> floating_value -> 'a) ->           (* floating *)
  (Ctype.ctype -> pointer_value -> 'a) ->                   (* pointer *)
  (mem_value list -> 'a) ->                                 (* array *)
  (Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> 'a) ->  (* struct *)
  (Symbol.sym -> Symbol.identifier -> mem_value -> 'a) ->   (* union *)
  'a
```

**Solution:** Use `case_mem_value` to build structured JSON:
```ocaml
let rec json_mem_value (mval : Impl_mem.mem_value) : Yojson.Safe.t =
  Impl_mem.case_mem_value mval
    (* unspecified *)
    (fun cty -> `Assoc [
      ("tag", `String "MVunspecified");
      ("ctype", json_ctype cty)
    ])
    (* concurrent read - shouldn't occur in sequential *)
    (fun () -> `Assoc [("tag", `String "MVconcurrent")])
    (* integer *)
    (fun ity ival -> `Assoc [
      ("tag", `String "MVinteger");
      ("int_type", json_integer_type ity);
      ("value", json_integer_value ival)
    ])
    (* floating *)
    (fun fty fval -> `Assoc [
      ("tag", `String "MVfloating");
      ("float_type", json_floating_type fty);
      ("value", json_floating_value fval)
    ])
    (* pointer *)
    (fun cty pval -> `Assoc [
      ("tag", `String "MVpointer");
      ("ctype", json_ctype cty);
      ("value", json_pointer_value pval)
    ])
    (* array *)
    (fun mvals -> `Assoc [
      ("tag", `String "MVarray");
      ("elements", `List (List.map json_mem_value mvals))
    ])
    (* struct *)
    (fun tag_sym members -> `Assoc [
      ("tag", `String "MVstruct");
      ("struct_tag", json_sym tag_sym);
      ("members", `List (List.map (fun (id, cty, mval) ->
        `Assoc [
          ("name", json_identifier id);
          ("ctype", json_ctype cty);
          ("value", json_mem_value mval)
        ]) members))
    ])
    (* union *)
    (fun tag_sym member_id mval -> `Assoc [
      ("tag", `String "MVunion");
      ("union_tag", json_sym tag_sym);
      ("member", json_identifier member_id);
      ("value", json_mem_value mval)
    ])
```

Then update `json_object_value` to use `json_mem_value` instead of `pp_to_string`.

**Dependencies:** Need `json_integer_value` and `json_floating_value` functions. These may need similar treatment if they're currently stringified.

---

### 4. Missing `impl` Field

**Current State:** The `impl` field is not serialized in `json_file`.

**Location:** `json_core.ml:898-915`
```ocaml
let json_file (file : ('bty, 'a) generic_file) : Yojson.Safe.t =
  (* ... *)
  `Assoc [
    ("main", main_json);
    ("tagDefs", tagdefs_json);
    ("stdlib", stdlib_json);
    ("globs", globs_json);
    ("funs", funs_json);
    ("funinfo", funinfo_json)
    (* impl is MISSING *)
    (* extern is MISSING *)
  ]
```

**Type Definition:** From `core.ott:489-492`
```ocaml
type generic_impl_decl 'bty =
  | Def of core_base_type * generic_pexpr 'bty Symbol.sym
  | IFun of core_base_type * list (Symbol.sym * core_base_type) * generic_pexpr 'bty Symbol.sym

type generic_impl 'bty = map Implementation.implementation_constant (generic_impl_decl 'bty)
```

**Solution:** Add `json_impl_decl` and `json_impl` functions:
```ocaml
let json_impl_decl = function
  | Def (bty, pe) ->
      `Assoc [
        ("tag", `String "Def");
        ("type", json_core_base_type bty);
        ("expr", json_pexpr pe)
      ]
  | IFun (bty, params, pe) ->
      `Assoc [
        ("tag", `String "IFun");
        ("return_type", json_core_base_type bty);
        ("params", `List (List.map (fun (sym, bty) ->
          `Assoc [("symbol", json_sym sym); ("type", json_core_base_type bty)]
        ) params));
        ("body", json_pexpr pe)
      ]

let json_impl impl =
  `List (List.map (fun (ic, decl) ->
    `Assoc [
      ("constant", `String (Implementation.string_of_implementation_constant ic));
      ("decl", json_impl_decl decl)
    ]
  ) (Pmap.bindings_list impl))
```

Then add to `json_file`:
```ocaml
let impl_json = json_impl file.impl in
(* ... *)
`Assoc [
  (* ... *)
  ("impl", impl_json);
  (* ... *)
]
```

---

### 5. Missing `extern` Field

**Current State:** The `extern` field is not serialized in `json_file`.

**Type Definition:** From `core.ott:520-536`
```ocaml
type linking_kind =
  | LK_none
  | LK_tentative of Symbol.sym
  | LK_normal of Symbol.sym

type extern_map = map Symbol.identifier (list Symbol.sym * linking_kind)
```

**Solution:** Add `json_linking_kind` and `json_extern` functions:
```ocaml
let json_linking_kind = function
  | LK_none -> `Assoc [("tag", `String "LK_none")]
  | LK_tentative sym ->
      `Assoc [("tag", `String "LK_tentative"); ("symbol", json_sym sym)]
  | LK_normal sym ->
      `Assoc [("tag", `String "LK_normal"); ("symbol", json_sym sym)]

let json_extern extern =
  `List (List.map (fun (id, (syms, lk)) ->
    `Assoc [
      ("identifier", json_identifier id);
      ("symbols", `List (List.map json_sym syms));
      ("linking_kind", json_linking_kind lk)
    ]
  ) (Pmap.bindings_list extern))
```

Then add to `json_file`:
```ocaml
let extern_json = json_extern file.extern in
(* ... *)
`Assoc [
  (* ... *)
  ("extern", extern_json);
]
```

---

## Implementation Order

1. **Memop serialization** (Issue 1) - Most impactful, affects interpretation
2. **Pure memop serialization** (Issue 2) - Same pattern, quick follow-up
3. **impl field** (Issue 4) - Straightforward addition
4. **extern field** (Issue 5) - Straightforward addition
5. **mem_value serialization** (Issue 3) - Most complex due to recursion and dependencies

## Testing

After each change:
1. Rebuild Cerberus: `make cerberus`
2. Run parser tests: `./scripts/test_parser.sh --quick`
3. Run PP tests: `./scripts/test_pp.sh --max 100`

Note: PP tests will initially fail after structured JSON changes until the Lean parser is updated.

## Lean Parser Updates Required

For each Cerberus change, corresponding Lean parser updates are needed:

1. **Memop:** Update `parseMemop` in `Parser.lean` to parse structured JSON
2. **Pure memop:** Update `parsePureMemop` (if exists) or add it
3. **impl:** Add `parseImplDecl` and update `parseFile` to populate `impl` field
4. **extern:** Add `parseLinkingKind`, `parseExtern` and update `parseFile`
5. **mem_value:** Add `parseMemValue` and update `parseObjectValue` for OVstruct/OVunion
